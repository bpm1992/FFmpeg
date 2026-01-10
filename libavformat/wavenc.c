/*
 * WAV muxer
 * Copyright (c) 2001, 2002 Fabrice Bellard
 *
 * Sony Wave64 muxer
 * Copyright (c) 2012 Paul B Mahol
 *
 * WAV muxer RF64 support
 * Copyright (c) 2013 Daniel Verkamp <daniel@drv.nu>
 *
 * EBU Tech 3285 - Supplement 3 - Peak Envelope Chunk encoder
 * Copyright (c) 2014 Georg Lippitsch <georg.lippitsch@gmx.at>
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include "config_components.h"

#include <stdint.h>
#include <string.h>

#include "libavcodec/avcodec.h"
#include "libavutil/avstring.h"
#include "libavutil/dict.h"
#include "libavutil/common.h"
#include "libavutil/intreadwrite.h"
#include "libavutil/mathematics.h"
#include "libavutil/opt.h"
#include "libavutil/time.h"
#include "libavutil/time_internal.h"

#include "avformat.h"
#include "avio.h"
#include "avio_internal.h"
#include "internal.h"
#include "riff.h"

#define RF64_AUTO   (-1)
#define RF64_NEVER  0
#define RF64_ALWAYS 1

typedef enum {
    PEAK_OFF = 0,
    PEAK_ON,
    PEAK_ONLY
} PeakType;

typedef enum {
    PEAK_FORMAT_UINT8 = 1,
    PEAK_FORMAT_UINT16
} PeakFormat;

typedef struct WAVMuxContext {
    const AVClass *class;
    int64_t data;
    int64_t fact_pos;
    int64_t mext_pos;          /* MEXT chunk position for MP2 */
    int64_t ds64;
    int64_t minpts;
    int64_t maxpts;
    int16_t *peak_maxpos, *peak_maxneg;
    uint32_t peak_num_frames;
    unsigned peak_outbuf_size;
    uint32_t peak_outbuf_bytes;
    unsigned size_increment;
    uint8_t *peak_output;
    int last_duration;
    int write_bext;
    int write_peak;
    int rf64;
    int peak_block_size;
    int peak_format;
    int peak_block_pos;

    /* MP2 peak calculation support */
    AVCodecContext *mp2_dec_ctx;  /* decoder context for MP2 peak calculation */
    AVFrame *mp2_frame;           /* frame for decoded MP2 samples */
    AVPacket *mp2_pkt;            /* packet for MP2 decoding */
    int is_mp2_peak;              /* flag for MP2 peak mode */
    int peak_ppv;
    int peak_bps;
} WAVMuxContext;

#if CONFIG_WAV_MUXER
static inline void bwf_write_bext_string(AVFormatContext *s, const char *key, int maxlen)
{
    AVDictionaryEntry *tag;
    size_t len = 0;

    if (tag = av_dict_get(s->metadata, key, NULL, 0)) {
        len = strlen(tag->value);
        len = FFMIN(len, maxlen);
        avio_write(s->pb, tag->value, len);
    }

    ffio_fill(s->pb, 0, maxlen - len);
}

static void bwf_write_bext_chunk(AVFormatContext *s)
{
    AVDictionaryEntry *tmp_tag;
    uint64_t time_reference = 0;
    int64_t bext = ff_start_tag(s->pb, "bext");

    bwf_write_bext_string(s, "description", 256);
    bwf_write_bext_string(s, "originator", 32);
    bwf_write_bext_string(s, "originator_reference", 32);
    bwf_write_bext_string(s, "origination_date", 10);
    bwf_write_bext_string(s, "origination_time", 8);

    if (tmp_tag = av_dict_get(s->metadata, "time_reference", NULL, 0))
        time_reference = strtoll(tmp_tag->value, NULL, 10);
    avio_wl64(s->pb, time_reference);
    avio_wl16(s->pb, 1);  // set version to 1

    if ((tmp_tag = av_dict_get(s->metadata, "umid", NULL, 0)) && strlen(tmp_tag->value) > 2) {
        unsigned char umidpart_str[17] = {0};
        int64_t i;
        uint64_t umidpart;
        size_t len = strlen(tmp_tag->value+2);

        for (i = 0; i < len/16; i++) {
            memcpy(umidpart_str, tmp_tag->value + 2 + (i*16), 16);
            umidpart = strtoll(umidpart_str, NULL, 16);
            avio_wb64(s->pb, umidpart);
        }
        ffio_fill(s->pb, 0, 64 - i*8);
    } else
        ffio_fill(s->pb, 0, 64); // zero UMID

    ffio_fill(s->pb, 0, 190); // Reserved

    if (tmp_tag = av_dict_get(s->metadata, "coding_history", NULL, 0))
        avio_put_str(s->pb, tmp_tag->value);

    ff_end_tag(s->pb, bext);
}

/**
 * Write MEXT (MPEG Extension) chunk for MP2 WAV files
 * This chunk is required by Rivendell for MP2-encoded WAV files
 * with peak envelope data in the LEVL chunk.
 *
 * MEXT Chunk Structure (12 bytes of data):
 *   - sound_information (2 bytes): flags for homogenous, no padding, etc.
 *   - frame_size (2 bytes): MPEG frame size without padding
 *   - ancillary_data_length (2 bytes): ancillary data length
 *   - ancillary_data_def (2 bytes): flags for left/right energy presence
 *   - reserved (4 bytes): reserved for future use
 */
static void bwf_write_mext_chunk(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVCodecParameters *par = s->streams[0]->codecpar;
    int64_t mext;
    uint16_t sound_info = 0;
    uint16_t frame_size = 0;
    uint16_t anc_data_len = 0;
    uint16_t anc_data_def = 0;

    /* Only write MEXT for MP2 */
    if (par->codec_id != AV_CODEC_ID_MP2)
        return;

    mext = ff_start_tag(s->pb, "mext");

    /*
     * sound_information flags:
     * bit 0: Homogenous sound data (1 = all frames same configuration)
     * bit 1: No padding in frames (1 = padding bit always 0)
     * bit 2: Rate hacked (non-standard sample rate)
     * bit 3: Free format bitstream
     */
    sound_info = 0x0001;  /* Homogenous sound data */

    /*
     * Calculate approximate MPEG frame size
     * For MPEG-1 Layer 2: frame_size = 144 * bitrate / sample_rate
     * Standard frame is 1152 samples
     */
    if (par->bit_rate > 0 && par->sample_rate > 0) {
        frame_size = (uint16_t)(144 * par->bit_rate / par->sample_rate);
    } else {
        /* Default to common frame size for 256kbps @ 44100Hz stereo */
        frame_size = 836;
    }

    /*
     * ancillary_data_def flags for peak data presence:
     * bit 0: Left channel energy present in ancillary data
     * bit 1: Private byte present
     * bit 2: Right channel energy present in ancillary data
     *
     * When write_peak is enabled, we set both energy flags to indicate
     * peak data will be in the LEVL chunk (not ancillary data, but Rivendell
     * uses this as a compatibility indicator)
     */
    if (wav->write_peak) {
        anc_data_def = 0x0005;  /* Left + Right energy flags */
        anc_data_len = 4;       /* 2 bytes per channel for peak values */
    }

    avio_wl16(s->pb, sound_info);        /* sound_information */
    avio_wl16(s->pb, frame_size);        /* frame_size */
    avio_wl16(s->pb, anc_data_len);      /* ancillary_data_length */
    avio_wl16(s->pb, anc_data_def);      /* ancillary_data_def */
    avio_wl32(s->pb, 0);                 /* reserved */

    ff_end_tag(s->pb, mext);

    wav->mext_pos = mext;
}

static av_cold void wav_deinit(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;

    av_freep(&wav->peak_maxpos);
    av_freep(&wav->peak_maxneg);
    av_freep(&wav->peak_output);

    /* Clean up MP2 decoder resources */
    if (wav->mp2_dec_ctx) {
        avcodec_free_context(&wav->mp2_dec_ctx);
    }
    if (wav->mp2_frame) {
        av_frame_free(&wav->mp2_frame);
    }
    if (wav->mp2_pkt) {
        av_packet_free(&wav->mp2_pkt);
    }
}

static av_cold int peak_init_writer(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVCodecParameters *par = s->streams[0]->codecpar;

    /* Handle MP2 codec - decode and calculate peaks from decoded PCM */
    if (par->codec_id == AV_CODEC_ID_MP2) {
        const AVCodec *codec = avcodec_find_decoder(AV_CODEC_ID_MP2);
        int ret;

        if (!codec) {
            av_log(s, AV_LOG_ERROR, "MP2 decoder not found for Peak Chunk calculation\n");
            return AVERROR_DECODER_NOT_FOUND;
        }

        wav->mp2_dec_ctx = avcodec_alloc_context3(codec);
        if (!wav->mp2_dec_ctx) {
            av_log(s, AV_LOG_ERROR, "Failed to allocate MP2 decoder context\n");
            return AVERROR(ENOMEM);
        }

        /* Set decoder parameters from stream */
        wav->mp2_dec_ctx->sample_rate = par->sample_rate;
        wav->mp2_dec_ctx->ch_layout = par->ch_layout;

        ret = avcodec_open2(wav->mp2_dec_ctx, codec, NULL);
        if (ret < 0) {
            av_log(s, AV_LOG_ERROR, "Failed to open MP2 decoder: %s\n", av_err2str(ret));
            avcodec_free_context(&wav->mp2_dec_ctx);
            return ret;
        }

        wav->mp2_frame = av_frame_alloc();
        if (!wav->mp2_frame) {
            avcodec_free_context(&wav->mp2_dec_ctx);
            return AVERROR(ENOMEM);
        }

        wav->mp2_pkt = av_packet_alloc();
        if (!wav->mp2_pkt) {
            av_frame_free(&wav->mp2_frame);
            avcodec_free_context(&wav->mp2_dec_ctx);
            return AVERROR(ENOMEM);
        }

        wav->is_mp2_peak = 1;
        wav->peak_bps = 2;  /* 16-bit samples after decoding */

        /* For Rivendell compatibility, use block size of 1152 (MPEG frame size)
         * if user hasn't specified a different value */
        if (wav->peak_block_size == 256) {  /* default value */
            wav->peak_block_size = 1152;
            av_log(s, AV_LOG_INFO, "Setting peak_block_size to 1152 for MP2 (Rivendell compatible)\n");
        }

        av_log(s, AV_LOG_INFO, "MP2 Peak Chunk support enabled - decoding frames for peak calculation\n");
    } else if (par->codec_id != AV_CODEC_ID_PCM_S8 &&
               par->codec_id != AV_CODEC_ID_PCM_S16LE &&
               par->codec_id != AV_CODEC_ID_PCM_U8 &&
               par->codec_id != AV_CODEC_ID_PCM_U16LE) {
        av_log(s, AV_LOG_ERROR, "Codec %s not supported for Peak Chunk\n",
               avcodec_get_name(par->codec_id));
        return -1;
    } else {
        wav->peak_bps = av_get_bits_per_sample(par->codec_id) / 8;
    }

    if (wav->peak_bps == 1 && wav->peak_format == PEAK_FORMAT_UINT16) {
        av_log(s, AV_LOG_ERROR,
               "Writing 16 bit peak for 8 bit audio does not make sense\n");
        return AVERROR(EINVAL);
    }
    if (par->ch_layout.nb_channels > INT_MAX / (wav->peak_bps * wav->peak_ppv))
        return AVERROR(ERANGE);
    wav->size_increment = par->ch_layout.nb_channels * wav->peak_bps * wav->peak_ppv;

    wav->peak_maxpos = av_calloc(par->ch_layout.nb_channels, sizeof(*wav->peak_maxpos));
    wav->peak_maxneg = av_calloc(par->ch_layout.nb_channels, sizeof(*wav->peak_maxneg));
    if (!wav->peak_maxpos || !wav->peak_maxneg)
        goto nomem;

    return 0;

nomem:
    av_log(s, AV_LOG_ERROR, "Out of memory\n");
    return AVERROR(ENOMEM);
}

static int peak_write_frame(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVCodecParameters *par = s->streams[0]->codecpar;
    unsigned new_size = wav->peak_outbuf_bytes + wav->size_increment;
    uint8_t *tmp;
    int c;

    if (new_size > INT_MAX) {
        wav->write_peak = PEAK_OFF;
        return AVERROR(ERANGE);
    }
    tmp = av_fast_realloc(wav->peak_output, &wav->peak_outbuf_size, new_size);
    if (!tmp) {
        wav->write_peak = PEAK_OFF;
        return AVERROR(ENOMEM);
    }
    wav->peak_output = tmp;

    for (c = 0; c < par->ch_layout.nb_channels; c++) {
        wav->peak_maxneg[c] = -wav->peak_maxneg[c];

        if (wav->peak_bps == 2 && wav->peak_format == PEAK_FORMAT_UINT8) {
            wav->peak_maxpos[c] = wav->peak_maxpos[c] / 256;
            wav->peak_maxneg[c] = wav->peak_maxneg[c] / 256;
        }

        if (wav->peak_ppv == 1)
            wav->peak_maxpos[c] =
                FFMAX(wav->peak_maxpos[c], wav->peak_maxneg[c]);

        if (wav->peak_format == PEAK_FORMAT_UINT8) {
            wav->peak_output[wav->peak_outbuf_bytes++] =
                wav->peak_maxpos[c];
            if (wav->peak_ppv == 2) {
                wav->peak_output[wav->peak_outbuf_bytes++] =
                    wav->peak_maxneg[c];
            }
        } else {
            AV_WL16(wav->peak_output + wav->peak_outbuf_bytes,
                    wav->peak_maxpos[c]);
            wav->peak_outbuf_bytes += 2;
            if (wav->peak_ppv == 2) {
                AV_WL16(wav->peak_output + wav->peak_outbuf_bytes,
                        wav->peak_maxneg[c]);
                wav->peak_outbuf_bytes += 2;
            }
        }
        wav->peak_maxpos[c] = 0;
        wav->peak_maxneg[c] = 0;
    }
    wav->peak_num_frames++;

    return 0;
}

static int peak_write_chunk(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVIOContext *pb = s->pb;
    AVCodecParameters *par = s->streams[0]->codecpar;
    int64_t peak = ff_start_tag(s->pb, "levl");
    int64_t now0;
    time_t now_secs;
    char timestamp[28];

    /* Peak frame of incomplete block at end */
    if (wav->peak_block_pos) {
        int ret = peak_write_frame(s);
        if (ret < 0)
            return ret;
    }

    memset(timestamp, 0, sizeof(timestamp));
    if (!(s->flags & AVFMT_FLAG_BITEXACT)) {
        struct tm tmpbuf;
        av_log(s, AV_LOG_INFO, "Writing local time and date to Peak Envelope Chunk\n");
        now0 = av_gettime();
        now_secs = now0 / 1000000;
        if (strftime(timestamp, sizeof(timestamp), "%Y:%m:%d:%H:%M:%S:", localtime_r(&now_secs, &tmpbuf))) {
            av_strlcatf(timestamp, sizeof(timestamp), "%03d", (int)((now0 / 1000) % 1000));
        } else {
            av_log(s, AV_LOG_ERROR, "Failed to write timestamp\n");
            return -1;
        }
    }

    avio_wl32(pb, 1);                           /* version */
    avio_wl32(pb, wav->peak_format);            /* 8 or 16 bit */
    avio_wl32(pb, wav->peak_ppv);               /* positive and negative */
    avio_wl32(pb, wav->peak_block_size);        /* frames per value */
    avio_wl32(pb, par->ch_layout.nb_channels);  /* number of channels */
    avio_wl32(pb, wav->peak_num_frames);        /* number of peak frames */
    avio_wl32(pb, -1);                          /* audio sample frame position (not implemented) */
    avio_wl32(pb, 128);                         /* equal to size of header */
    avio_write(pb, timestamp, 28);              /* ASCII time stamp */
    ffio_fill(pb, 0, 60);

    avio_write(pb, wav->peak_output, wav->peak_outbuf_bytes);

    ff_end_tag(pb, peak);

    if (!wav->data)
        wav->data = peak;

    return 0;
}

static int wav_write_header(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVIOContext *pb = s->pb;
    int64_t fmt;

    if (s->nb_streams != 1) {
        av_log(s, AV_LOG_ERROR, "WAVE files have exactly one stream\n");
        return AVERROR(EINVAL);
    }

    if (wav->rf64 == RF64_ALWAYS) {
        ffio_wfourcc(pb, "RF64");
        avio_wl32(pb, -1); /* RF64 chunk size: use size in ds64 */
    } else {
        ffio_wfourcc(pb, "RIFF");
        avio_wl32(pb, -1); /* file length */
    }

    ffio_wfourcc(pb, "WAVE");

    if (wav->rf64 != RF64_NEVER) {
        /* write empty ds64 chunk or JUNK chunk to reserve space for ds64 */
        ffio_wfourcc(pb, wav->rf64 == RF64_ALWAYS ? "ds64" : "JUNK");
        avio_wl32(pb, 28); /* chunk size */
        wav->ds64 = avio_tell(pb);
        ffio_fill(pb, 0, 28);
    }

    if (wav->write_peak != PEAK_ONLY) {
        /* format header */
        fmt = ff_start_tag(pb, "fmt ");
        if (ff_put_wav_header(s, pb, s->streams[0]->codecpar, 0) < 0) {
            av_log(s, AV_LOG_ERROR, "Codec %s not supported in WAVE format\n",
                   avcodec_get_name(s->streams[0]->codecpar->codec_id));
            return AVERROR(ENOSYS);
        }
        ff_end_tag(pb, fmt);
    }

    if (s->streams[0]->codecpar->codec_tag != 0x01 /* hence for all other than PCM */
        && (s->pb->seekable & AVIO_SEEKABLE_NORMAL)) {
        wav->fact_pos = ff_start_tag(pb, "fact");
        avio_wl32(pb, 0);
        ff_end_tag(pb, wav->fact_pos);
    }

    /* Write MEXT chunk for MP2 WAV files (required by Rivendell) */
    if (s->streams[0]->codecpar->codec_id == AV_CODEC_ID_MP2) {
        bwf_write_mext_chunk(s);
    }

    if (wav->write_bext)
        bwf_write_bext_chunk(s);

    if (wav->write_peak) {
        int ret;
        if ((ret = peak_init_writer(s)) < 0)
            return ret;
    }

    avpriv_set_pts_info(s->streams[0], 64, 1, s->streams[0]->codecpar->sample_rate);
    wav->maxpts = wav->last_duration = 0;
    wav->minpts = INT64_MAX;

    if (wav->write_peak != PEAK_ONLY) {
        /* info header */
        ff_riff_write_info(s);

        /* data header */
        wav->data = ff_start_tag(pb, "data");
    }

    return 0;
}

static int wav_write_packet(AVFormatContext *s, AVPacket *pkt)
{
    AVIOContext *pb  = s->pb;
    WAVMuxContext    *wav = s->priv_data;

    if (wav->write_peak != PEAK_ONLY)
        avio_write(pb, pkt->data, pkt->size);

    if (wav->write_peak) {
        if (wav->is_mp2_peak) {
            /* MP2: Decode the packet and calculate peaks from decoded samples */
            int ret;

            ret = avcodec_send_packet(wav->mp2_dec_ctx, pkt);
            if (ret < 0 && ret != AVERROR(EAGAIN) && ret != AVERROR_EOF) {
                av_log(s, AV_LOG_WARNING, "Error sending MP2 packet for peak calculation: %s\n",
                       av_err2str(ret));
            }

            while (ret >= 0) {
                ret = avcodec_receive_frame(wav->mp2_dec_ctx, wav->mp2_frame);
                if (ret == AVERROR(EAGAIN) || ret == AVERROR_EOF) {
                    break;
                } else if (ret < 0) {
                    av_log(s, AV_LOG_WARNING, "Error receiving decoded frame for peak calculation: %s\n",
                           av_err2str(ret));
                    break;
                }

                /* Calculate peaks from decoded samples (16-bit signed PCM) */
                {
                    int nb_samples = wav->mp2_frame->nb_samples;
                    int nb_channels = wav->mp2_frame->ch_layout.nb_channels;
                    int c, i;

                    /* Handle planar vs interleaved format */
                    if (av_sample_fmt_is_planar(wav->mp2_frame->format)) {
                        /* Planar format: separate buffer per channel */
                        for (i = 0; i < nb_samples; i++) {
                            for (c = 0; c < nb_channels; c++) {
                                int16_t sample;
                                if (wav->mp2_frame->format == AV_SAMPLE_FMT_S16P) {
                                    sample = ((int16_t *)wav->mp2_frame->extended_data[c])[i];
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_FLTP) {
                                    float fsample = ((float *)wav->mp2_frame->extended_data[c])[i];
                                    sample = (int16_t)(FFMIN(FFMAX(fsample, -1.0f), 1.0f) * 32767);
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_S32P) {
                                    sample = ((int32_t *)wav->mp2_frame->extended_data[c])[i] >> 16;
                                } else {
                                    sample = 0;
                                }
                                wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], sample);
                                wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], sample);
                            }
                            if (++wav->peak_block_pos == wav->peak_block_size) {
                                int write_ret = peak_write_frame(s);
                                if (write_ret < 0)
                                    return write_ret;
                                wav->peak_block_pos = 0;
                            }
                        }
                    } else {
                        /* Interleaved format */
                        int16_t *samples = (int16_t *)wav->mp2_frame->data[0];
                        float *fsamples = (float *)wav->mp2_frame->data[0];
                        int32_t *isamples = (int32_t *)wav->mp2_frame->data[0];

                        for (i = 0; i < nb_samples; i++) {
                            for (c = 0; c < nb_channels; c++) {
                                int16_t sample;
                                if (wav->mp2_frame->format == AV_SAMPLE_FMT_S16) {
                                    sample = samples[i * nb_channels + c];
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_FLT) {
                                    float fsample = fsamples[i * nb_channels + c];
                                    sample = (int16_t)(FFMIN(FFMAX(fsample, -1.0f), 1.0f) * 32767);
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_S32) {
                                    sample = isamples[i * nb_channels + c] >> 16;
                                } else {
                                    sample = 0;
                                }
                                wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], sample);
                                wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], sample);
                            }
                            if (++wav->peak_block_pos == wav->peak_block_size) {
                                int write_ret = peak_write_frame(s);
                                if (write_ret < 0)
                                    return write_ret;
                                wav->peak_block_pos = 0;
                            }
                        }
                    }
                }

                av_frame_unref(wav->mp2_frame);
            }
        } else {
            /* PCM: Original peak calculation */
            int c = 0;
            int i;
            for (i = 0; i < pkt->size; i += wav->peak_bps) {
                if (wav->peak_bps == 1) {
                    wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], *(int8_t*)(pkt->data + i));
                    wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], *(int8_t*)(pkt->data + i));
                } else {
                    wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], (int16_t)AV_RL16(pkt->data + i));
                    wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], (int16_t)AV_RL16(pkt->data + i));
                }
                if (++c == s->streams[0]->codecpar->ch_layout.nb_channels) {
                    c = 0;
                    if (++wav->peak_block_pos == wav->peak_block_size) {
                        int ret = peak_write_frame(s);
                        if (ret < 0)
                            return ret;
                        wav->peak_block_pos = 0;
                    }
                }
            }
        }
    }

    if(pkt->pts != AV_NOPTS_VALUE) {
        wav->minpts        = FFMIN(wav->minpts, pkt->pts);
        wav->maxpts        = FFMAX(wav->maxpts, pkt->pts);
        wav->last_duration = pkt->duration;
    } else
        av_log(s, AV_LOG_ERROR, "wav_write_packet: NOPTS\n");
    return 0;
}

static int wav_write_trailer(AVFormatContext *s)
{
    AVIOContext *pb  = s->pb;
    WAVMuxContext    *wav = s->priv_data;
    int64_t file_size, data_size;
    int64_t number_of_samples = 0;
    int rf64 = 0;
    int ret = 0;

    /* Flush MP2 decoder to get any remaining samples for peak calculation */
    if (wav->write_peak && wav->is_mp2_peak && wav->mp2_dec_ctx) {
        int flush_ret;

        /* Send NULL packet to flush decoder */
        flush_ret = avcodec_send_packet(wav->mp2_dec_ctx, NULL);
        if (flush_ret >= 0) {
            while (1) {
                flush_ret = avcodec_receive_frame(wav->mp2_dec_ctx, wav->mp2_frame);
                if (flush_ret == AVERROR_EOF || flush_ret == AVERROR(EAGAIN))
                    break;
                if (flush_ret < 0)
                    break;

                /* Process remaining decoded samples */
                {
                    int nb_samples = wav->mp2_frame->nb_samples;
                    int nb_channels = wav->mp2_frame->ch_layout.nb_channels;
                    int c, i;

                    if (av_sample_fmt_is_planar(wav->mp2_frame->format)) {
                        for (i = 0; i < nb_samples; i++) {
                            for (c = 0; c < nb_channels; c++) {
                                int16_t sample;
                                if (wav->mp2_frame->format == AV_SAMPLE_FMT_S16P) {
                                    sample = ((int16_t *)wav->mp2_frame->extended_data[c])[i];
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_FLTP) {
                                    float fsample = ((float *)wav->mp2_frame->extended_data[c])[i];
                                    sample = (int16_t)(FFMIN(FFMAX(fsample, -1.0f), 1.0f) * 32767);
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_S32P) {
                                    sample = ((int32_t *)wav->mp2_frame->extended_data[c])[i] >> 16;
                                } else {
                                    sample = 0;
                                }
                                wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], sample);
                                wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], sample);
                            }
                            if (++wav->peak_block_pos == wav->peak_block_size) {
                                peak_write_frame(s);
                                wav->peak_block_pos = 0;
                            }
                        }
                    } else {
                        int16_t *samples = (int16_t *)wav->mp2_frame->data[0];
                        float *fsamples = (float *)wav->mp2_frame->data[0];
                        int32_t *isamples = (int32_t *)wav->mp2_frame->data[0];

                        for (i = 0; i < nb_samples; i++) {
                            for (c = 0; c < nb_channels; c++) {
                                int16_t sample;
                                if (wav->mp2_frame->format == AV_SAMPLE_FMT_S16) {
                                    sample = samples[i * nb_channels + c];
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_FLT) {
                                    float fsample = fsamples[i * nb_channels + c];
                                    sample = (int16_t)(FFMIN(FFMAX(fsample, -1.0f), 1.0f) * 32767);
                                } else if (wav->mp2_frame->format == AV_SAMPLE_FMT_S32) {
                                    sample = isamples[i * nb_channels + c] >> 16;
                                } else {
                                    sample = 0;
                                }
                                wav->peak_maxpos[c] = FFMAX(wav->peak_maxpos[c], sample);
                                wav->peak_maxneg[c] = FFMIN(wav->peak_maxneg[c], sample);
                            }
                            if (++wav->peak_block_pos == wav->peak_block_size) {
                                peak_write_frame(s);
                                wav->peak_block_pos = 0;
                            }
                        }
                    }
                }
                av_frame_unref(wav->mp2_frame);
            }
        }
    }

    if (s->pb->seekable & AVIO_SEEKABLE_NORMAL) {
        if (wav->write_peak != PEAK_ONLY && avio_tell(pb) - wav->data < UINT32_MAX) {
            ff_end_tag(pb, wav->data);
        }

        if (wav->write_peak && wav->peak_output) {
            ret = peak_write_chunk(s);
        }

        /* update file size */
        file_size = avio_tell(pb);
        data_size = file_size - wav->data;
        if (wav->rf64 == RF64_ALWAYS || (wav->rf64 == RF64_AUTO && file_size - 8 > UINT32_MAX)) {
            rf64 = 1;
        } else if (file_size - 8 <= UINT32_MAX) {
            avio_seek(pb, 4, SEEK_SET);
            avio_wl32(pb, (uint32_t)(file_size - 8));
            avio_seek(pb, file_size, SEEK_SET);
        } else {
            av_log(s, AV_LOG_ERROR,
                   "Filesize %"PRId64" invalid for wav, output file will be broken\n",
                   file_size);
        }
        number_of_samples = av_rescale_q(wav->maxpts - wav->minpts + wav->last_duration,
                                       s->streams[0]->time_base,
                                       av_make_q(1, s->streams[0]->codecpar->sample_rate));

        if(s->streams[0]->codecpar->codec_tag != 0x01) {
            /* Update num_samps in fact chunk */
            avio_seek(pb, wav->fact_pos, SEEK_SET);
            if (rf64 || (wav->rf64 == RF64_AUTO && number_of_samples > UINT32_MAX)) {
                rf64 = 1;
                avio_wl32(pb, -1);
            } else {
                avio_wl32(pb, number_of_samples);
                avio_seek(pb, file_size, SEEK_SET);
            }
        }

        if (rf64) {
            /* overwrite RIFF with RF64 */
            avio_seek(pb, 0, SEEK_SET);
            ffio_wfourcc(pb, "RF64");
            avio_wl32(pb, -1);

            /* write ds64 chunk (overwrite JUNK if rf64 == RF64_AUTO) */
            avio_seek(pb, wav->ds64 - 8, SEEK_SET);
            ffio_wfourcc(pb, "ds64");
            avio_wl32(pb, 28);                  /* ds64 chunk size */
            avio_wl64(pb, file_size - 8);       /* RF64 chunk size */
            avio_wl64(pb, data_size);           /* data chunk size */
            avio_wl64(pb, number_of_samples);   /* fact chunk number of samples */
            avio_wl32(pb, 0);                   /* number of table entries for non-'data' chunks */

            /* write -1 in data chunk size */
            avio_seek(pb, wav->data - 4, SEEK_SET);
            avio_wl32(pb, -1);

            avio_seek(pb, file_size, SEEK_SET);
        }
    }

    return ret;
}

#define OFFSET(x) offsetof(WAVMuxContext, x)
#define ENC AV_OPT_FLAG_ENCODING_PARAM
static const AVOption options[] = {
    { "write_bext", "Write BEXT chunk.", OFFSET(write_bext), AV_OPT_TYPE_BOOL, { .i64 = 0 }, 0, 1, ENC },
    { "write_peak", "Write Peak Envelope chunk.",            OFFSET(write_peak), AV_OPT_TYPE_INT, { .i64 = 0 }, 0, 2, ENC, "peak" },
    { "off",        "Do not write peak chunk.",              0,                  AV_OPT_TYPE_CONST, { .i64 = PEAK_OFF  }, 0, 0, ENC, "peak" },
    { "on",         "Append peak chunk after wav data.",     0,                  AV_OPT_TYPE_CONST, { .i64 = PEAK_ON   }, 0, 0, ENC, "peak" },
    { "only",       "Write only peak chunk, omit wav data.", 0,                  AV_OPT_TYPE_CONST, { .i64 = PEAK_ONLY }, 0, 0, ENC, "peak" },
    { "rf64",       "Use RF64 header rather than RIFF for large files.",    OFFSET(rf64), AV_OPT_TYPE_INT,   { .i64 = RF64_NEVER  },-1, 1, ENC, "rf64" },
    { "auto",       "Write RF64 header if file grows large enough.",        0,            AV_OPT_TYPE_CONST, { .i64 = RF64_AUTO   }, 0, 0, ENC, "rf64" },
    { "always",     "Always write RF64 header regardless of file size.",    0,            AV_OPT_TYPE_CONST, { .i64 = RF64_ALWAYS }, 0, 0, ENC, "rf64" },
    { "never",      "Never write RF64 header regardless of file size.",     0,            AV_OPT_TYPE_CONST, { .i64 = RF64_NEVER  }, 0, 0, ENC, "rf64" },
    { "peak_block_size", "Number of audio samples used to generate each peak frame.",   OFFSET(peak_block_size), AV_OPT_TYPE_INT, { .i64 = 256 }, 0, 65536, ENC },
    { "peak_format",     "The format of the peak envelope data (1: uint8, 2: uint16).", OFFSET(peak_format), AV_OPT_TYPE_INT,     { .i64 = PEAK_FORMAT_UINT16 }, PEAK_FORMAT_UINT8, PEAK_FORMAT_UINT16, ENC },
    { "peak_ppv",        "Number of peak points per peak value (1 or 2).",              OFFSET(peak_ppv), AV_OPT_TYPE_INT, { .i64 = 2 }, 1, 2, ENC },
    { NULL },
};

static const AVClass wav_muxer_class = {
    .class_name = "WAV muxer",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};

const AVOutputFormat ff_wav_muxer = {
    .name              = "wav",
    .long_name         = NULL_IF_CONFIG_SMALL("WAV / WAVE (Waveform Audio)"),
    .mime_type         = "audio/x-wav",
    .extensions        = "wav",
    .priv_data_size    = sizeof(WAVMuxContext),
    .audio_codec       = AV_CODEC_ID_PCM_S16LE,
    .video_codec       = AV_CODEC_ID_NONE,
    .write_header      = wav_write_header,
    .write_packet      = wav_write_packet,
    .write_trailer     = wav_write_trailer,
    .deinit            = wav_deinit,
    .flags             = AVFMT_TS_NONSTRICT,
    .codec_tag         = ff_wav_codec_tags_list,
    .priv_class        = &wav_muxer_class,
};
#endif /* CONFIG_WAV_MUXER */

#if CONFIG_W64_MUXER
#include "w64.h"

static void start_guid(AVIOContext *pb, const uint8_t *guid, int64_t *pos)
{
    *pos = avio_tell(pb);

    avio_write(pb, guid, 16);
    avio_wl64(pb, INT64_MAX);
}

static void end_guid(AVIOContext *pb, int64_t start)
{
    int64_t end, pos = avio_tell(pb);

    end = FFALIGN(pos, 8);
    ffio_fill(pb, 0, end - pos);
    avio_seek(pb, start + 16, SEEK_SET);
    avio_wl64(pb, end - start);
    avio_seek(pb, end, SEEK_SET);
}

static int w64_write_header(AVFormatContext *s)
{
    WAVMuxContext *wav = s->priv_data;
    AVIOContext *pb = s->pb;
    int64_t start;
    int ret;

    avio_write(pb, ff_w64_guid_riff, sizeof(ff_w64_guid_riff));
    avio_wl64(pb, -1);
    avio_write(pb, ff_w64_guid_wave, sizeof(ff_w64_guid_wave));
    start_guid(pb, ff_w64_guid_fmt, &start);
    if ((ret = ff_put_wav_header(s, pb, s->streams[0]->codecpar, 0)) < 0) {
        av_log(s, AV_LOG_ERROR, "Codec %s not supported\n",
               avcodec_get_name(s->streams[0]->codecpar->codec_id));
        return ret;
    }
    end_guid(pb, start);

    if (s->streams[0]->codecpar->codec_tag != 0x01 /* hence for all other than PCM */
        && (s->pb->seekable & AVIO_SEEKABLE_NORMAL)) {
        start_guid(pb, ff_w64_guid_fact, &wav->fact_pos);
        avio_wl64(pb, 0);
        end_guid(pb, wav->fact_pos);
    }

    start_guid(pb, ff_w64_guid_data, &wav->data);

    return 0;
}

static int w64_write_trailer(AVFormatContext *s)
{
    AVIOContext    *pb = s->pb;
    WAVMuxContext *wav = s->priv_data;
    int64_t file_size;

    if (pb->seekable & AVIO_SEEKABLE_NORMAL) {
        end_guid(pb, wav->data);

        file_size = avio_tell(pb);
        avio_seek(pb, 16, SEEK_SET);
        avio_wl64(pb, file_size);

        if (s->streams[0]->codecpar->codec_tag != 0x01) {
            int64_t number_of_samples;

            number_of_samples = av_rescale(wav->maxpts - wav->minpts + wav->last_duration,
                                           s->streams[0]->codecpar->sample_rate * (int64_t)s->streams[0]->time_base.num,
                                           s->streams[0]->time_base.den);
            avio_seek(pb, wav->fact_pos + 24, SEEK_SET);
            avio_wl64(pb, number_of_samples);
        }

        avio_seek(pb, file_size, SEEK_SET);
    }

    return 0;
}

const AVOutputFormat ff_w64_muxer = {
    .name              = "w64",
    .long_name         = NULL_IF_CONFIG_SMALL("Sony Wave64"),
    .extensions        = "w64",
    .priv_data_size    = sizeof(WAVMuxContext),
    .audio_codec       = AV_CODEC_ID_PCM_S16LE,
    .video_codec       = AV_CODEC_ID_NONE,
    .write_header      = w64_write_header,
    .write_packet      = wav_write_packet,
    .write_trailer     = w64_write_trailer,
    .flags             = AVFMT_TS_NONSTRICT,
    .codec_tag         = ff_wav_codec_tags_list,
};
#endif /* CONFIG_W64_MUXER */
