-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3233__7
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3233__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:21:49.374357+00:00
-- url     : https://prove2.me/theorems/0dbdd217-bf1b-4f7a-a6f9-e8fe93879523
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233 (+6 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3233 (+6 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3300, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3301, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3302, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3303, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3310, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3312).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0302
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0472
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0474
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0475
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0477
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0144
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0146
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0147
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0148
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0303
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0304
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0306
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0308
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0309
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0312
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0314

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_32332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/80) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/16) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/64) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233112 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/128) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/128) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (117/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (123/640) (227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3233 | hx3233
  · rcases le_total tau.im (3/8 : ℝ) with hy3233 | hy3233
    · have hs32330 : InSquare (13/80) (29/80) (1/80) tau := by
        convert childLL hs hx3233 hy3233 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32330 | hx32330
      · rcases le_total tau.im (29/80 : ℝ) with hy32330 | hy32330
        · have hs323300 : InSquare (5/32) (57/160) (1/160) tau := by
            convert childLL hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323300 | hx323300
          · rcases le_total tau.im (57/160 : ℝ) with hy323300 | hy323300
            · have hs3233000 : InSquare (49/320) (113/320) (1/320) tau := by
                convert childLL hs323300 hx323300 hy323300 using 1 <;> norm_num
              exact Batch0302.cell2417.sound htau (by
                simp only [Batch0302.cell2417, Batch0302.tau2417, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233000 (by positivity) using 1 <;> norm_num)
            · have hs3233002 : InSquare (49/320) (23/64) (1/320) tau := by
                convert childUL hs323300 hx323300 hy323300 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233002 | hx3233002
              · rcases le_total tau.im (23/64 : ℝ) with hy3233002 | hy3233002
                · have hs32330020 : InSquare (97/640) (229/640) (1/640) tau := by
                    convert childLL hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3781.sound htau (by
                    simp only [Batch0472.cell3781, Batch0472.tau3781, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330020 (by positivity) using 1 <;> norm_num)
                · have hs32330022 : InSquare (97/640) (231/640) (1/640) tau := by
                    convert childUL hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3783.sound htau (by
                    simp only [Batch0472.cell3783, Batch0472.tau3783, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233002 | hy3233002
                · have hs32330021 : InSquare (99/640) (229/640) (1/640) tau := by
                    convert childLR hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3782.sound htau (by
                    simp only [Batch0472.cell3782, Batch0472.tau3782, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330021 (by positivity) using 1 <;> norm_num)
                · have hs32330023 : InSquare (99/640) (231/640) (1/640) tau := by
                    convert childUR hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0473.cell3784.sound htau (by
                    simp only [Batch0473.cell3784, Batch0473.tau3784, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323300 | hy323300
            · have hs3233001 : InSquare (51/320) (113/320) (1/320) tau := by
                convert childLR hs323300 hx323300 hy323300 using 1 <;> norm_num
              exact Batch0302.cell2418.sound htau (by
                simp only [Batch0302.cell2418, Batch0302.tau2418, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233001 (by positivity) using 1 <;> norm_num)
            · have hs3233003 : InSquare (51/320) (23/64) (1/320) tau := by
                convert childUR hs323300 hx323300 hy323300 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx3233003 | hx3233003
              · rcases le_total tau.im (23/64 : ℝ) with hy3233003 | hy3233003
                · have hs32330030 : InSquare (101/640) (229/640) (1/640) tau := by
                    convert childLL hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3785.sound htau (by
                    simp only [Batch0473.cell3785, Batch0473.tau3785, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330030 (by positivity) using 1 <;> norm_num)
                · have hs32330032 : InSquare (101/640) (231/640) (1/640) tau := by
                    convert childUL hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3787.sound htau (by
                    simp only [Batch0473.cell3787, Batch0473.tau3787, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233003 | hy3233003
                · have hs32330031 : InSquare (103/640) (229/640) (1/640) tau := by
                    convert childLR hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3786.sound htau (by
                    simp only [Batch0473.cell3786, Batch0473.tau3786, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330031 (by positivity) using 1 <;> norm_num)
                · have hs32330033 : InSquare (103/640) (231/640) (1/640) tau := by
                    convert childUR hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3788.sound htau (by
                    simp only [Batch0473.cell3788, Batch0473.tau3788, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330033 (by positivity) using 1 <;> norm_num)
        · have hs323302 : InSquare (5/32) (59/160) (1/160) tau := by
            convert childUL hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323302 | hx323302
          · rcases le_total tau.im (59/160 : ℝ) with hy323302 | hy323302
            · have hs3233020 : InSquare (49/320) (117/320) (1/320) tau := by
                convert childLL hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233020 | hx3233020
              · rcases le_total tau.im (117/320 : ℝ) with hy3233020 | hy3233020
                · have hs32330200 : InSquare (97/640) (233/640) (1/640) tau := by
                    convert childLL hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3801.sound htau (by
                    simp only [Batch0475.cell3801, Batch0475.tau3801, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330200 (by positivity) using 1 <;> norm_num)
                · have hs32330202 : InSquare (97/640) (47/128) (1/640) tau := by
                    convert childUL hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3803.sound htau (by
                    simp only [Batch0475.cell3803, Batch0475.tau3803, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3233020 | hy3233020
                · have hs32330201 : InSquare (99/640) (233/640) (1/640) tau := by
                    convert childLR hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3802.sound htau (by
                    simp only [Batch0475.cell3802, Batch0475.tau3802, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330201 (by positivity) using 1 <;> norm_num)
                · have hs32330203 : InSquare (99/640) (47/128) (1/640) tau := by
                    convert childUR hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3804.sound htau (by
                    simp only [Batch0475.cell3804, Batch0475.tau3804, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330203 (by positivity) using 1 <;> norm_num)
            · have hs3233022 : InSquare (49/320) (119/320) (1/320) tau := by
                convert childUL hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233022 | hx3233022
              · rcases le_total tau.im (119/320 : ℝ) with hy3233022 | hy3233022
                · have hs32330220 : InSquare (97/640) (237/640) (1/640) tau := by
                    convert childLL hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact Batch0476.cell3809.sound htau (by
                    simp only [Batch0476.cell3809, Batch0476.tau3809, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330220 (by positivity) using 1 <;> norm_num)
                · have hs32330222 : InSquare (97/640) (239/640) (1/640) tau := by
                    convert childUL hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact (outside_32330222 htau hs32330222).elim
              · rcases le_total tau.im (119/320 : ℝ) with hy3233022 | hy3233022
                · have hs32330221 : InSquare (99/640) (237/640) (1/640) tau := by
                    convert childLR hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact Batch0476.cell3810.sound htau (by
                    simp only [Batch0476.cell3810, Batch0476.tau3810, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330221 (by positivity) using 1 <;> norm_num)
                · have hs32330223 : InSquare (99/640) (239/640) (1/640) tau := by
                    convert childUR hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact (outside_32330223 htau hs32330223).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy323302 | hy323302
            · have hs3233021 : InSquare (51/320) (117/320) (1/320) tau := by
                convert childLR hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx3233021 | hx3233021
              · rcases le_total tau.im (117/320 : ℝ) with hy3233021 | hy3233021
                · have hs32330210 : InSquare (101/640) (233/640) (1/640) tau := by
                    convert childLL hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3805.sound htau (by
                    simp only [Batch0475.cell3805, Batch0475.tau3805, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330210 (by positivity) using 1 <;> norm_num)
                · have hs32330212 : InSquare (101/640) (47/128) (1/640) tau := by
                    convert childUL hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3807.sound htau (by
                    simp only [Batch0475.cell3807, Batch0475.tau3807, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3233021 | hy3233021
                · have hs32330211 : InSquare (103/640) (233/640) (1/640) tau := by
                    convert childLR hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3806.sound htau (by
                    simp only [Batch0475.cell3806, Batch0475.tau3806, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330211 (by positivity) using 1 <;> norm_num)
                · have hs32330213 : InSquare (103/640) (47/128) (1/640) tau := by
                    convert childUR hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0476.cell3808.sound htau (by
                    simp only [Batch0476.cell3808, Batch0476.tau3808, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330213 (by positivity) using 1 <;> norm_num)
            · have hs3233023 : InSquare (51/320) (119/320) (1/320) tau := by
                convert childUR hs323302 hx323302 hy323302 using 1 <;> norm_num
              exact (outside_3233023 htau hs3233023).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy32330 | hy32330
        · have hs323301 : InSquare (27/160) (57/160) (1/160) tau := by
            convert childLR hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323301 | hx323301
          · rcases le_total tau.im (57/160 : ℝ) with hy323301 | hy323301
            · have hs3233010 : InSquare (53/320) (113/320) (1/320) tau := by
                convert childLL hs323301 hx323301 hy323301 using 1 <;> norm_num
              exact Batch0302.cell2419.sound htau (by
                simp only [Batch0302.cell2419, Batch0302.tau2419, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233010 (by positivity) using 1 <;> norm_num)
            · have hs3233012 : InSquare (53/320) (23/64) (1/320) tau := by
                convert childUL hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx3233012 | hx3233012
              · rcases le_total tau.im (23/64 : ℝ) with hy3233012 | hy3233012
                · have hs32330120 : InSquare (21/128) (229/640) (1/640) tau := by
                    convert childLL hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3793.sound htau (by
                    simp only [Batch0474.cell3793, Batch0474.tau3793, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330120 (by positivity) using 1 <;> norm_num)
                · have hs32330122 : InSquare (21/128) (231/640) (1/640) tau := by
                    convert childUL hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3795.sound htau (by
                    simp only [Batch0474.cell3795, Batch0474.tau3795, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233012 | hy3233012
                · have hs32330121 : InSquare (107/640) (229/640) (1/640) tau := by
                    convert childLR hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3794.sound htau (by
                    simp only [Batch0474.cell3794, Batch0474.tau3794, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330121 (by positivity) using 1 <;> norm_num)
                · have hs32330123 : InSquare (107/640) (231/640) (1/640) tau := by
                    convert childUR hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3796.sound htau (by
                    simp only [Batch0474.cell3796, Batch0474.tau3796, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323301 | hy323301
            · have hs3233011 : InSquare (11/64) (113/320) (1/320) tau := by
                convert childLR hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233011 | hx3233011
              · rcases le_total tau.im (113/320 : ℝ) with hy3233011 | hy3233011
                · have hs32330110 : InSquare (109/640) (45/128) (1/640) tau := by
                    convert childLL hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3789.sound htau (by
                    simp only [Batch0473.cell3789, Batch0473.tau3789, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330110 (by positivity) using 1 <;> norm_num)
                · have hs32330112 : InSquare (109/640) (227/640) (1/640) tau := by
                    convert childUL hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3791.sound htau (by
                    simp only [Batch0473.cell3791, Batch0473.tau3791, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233011 | hy3233011
                · have hs32330111 : InSquare (111/640) (45/128) (1/640) tau := by
                    convert childLR hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3790.sound htau (by
                    simp only [Batch0473.cell3790, Batch0473.tau3790, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330111 (by positivity) using 1 <;> norm_num)
                · have hs32330113 : InSquare (111/640) (227/640) (1/640) tau := by
                    convert childUR hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0474.cell3792.sound htau (by
                    simp only [Batch0474.cell3792, Batch0474.tau3792, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330113 (by positivity) using 1 <;> norm_num)
            · have hs3233013 : InSquare (11/64) (23/64) (1/320) tau := by
                convert childUR hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233013 | hx3233013
              · rcases le_total tau.im (23/64 : ℝ) with hy3233013 | hy3233013
                · have hs32330130 : InSquare (109/640) (229/640) (1/640) tau := by
                    convert childLL hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3797.sound htau (by
                    simp only [Batch0474.cell3797, Batch0474.tau3797, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330130 (by positivity) using 1 <;> norm_num)
                · have hs32330132 : InSquare (109/640) (231/640) (1/640) tau := by
                    convert childUL hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3799.sound htau (by
                    simp only [Batch0474.cell3799, Batch0474.tau3799, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233013 | hy3233013
                · have hs32330131 : InSquare (111/640) (229/640) (1/640) tau := by
                    convert childLR hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3798.sound htau (by
                    simp only [Batch0474.cell3798, Batch0474.tau3798, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330131 (by positivity) using 1 <;> norm_num)
                · have hs32330133 : InSquare (111/640) (231/640) (1/640) tau := by
                    convert childUR hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0475.cell3800.sound htau (by
                    simp only [Batch0475.cell3800, Batch0475.tau3800, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330133 (by positivity) using 1 <;> norm_num)
        · have hs323303 : InSquare (27/160) (59/160) (1/160) tau := by
            convert childUR hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323303 | hx323303
          · rcases le_total tau.im (59/160 : ℝ) with hy323303 | hy323303
            · have hs3233030 : InSquare (53/320) (117/320) (1/320) tau := by
                convert childLL hs323303 hx323303 hy323303 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx3233030 | hx3233030
              · rcases le_total tau.im (117/320 : ℝ) with hy3233030 | hy3233030
                · have hs32330300 : InSquare (21/128) (233/640) (1/640) tau := by
                    convert childLL hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact Batch0476.cell3811.sound htau (by
                    simp only [Batch0476.cell3811, Batch0476.tau3811, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330300 (by positivity) using 1 <;> norm_num)
                · have hs32330302 : InSquare (21/128) (47/128) (1/640) tau := by
                    convert childUL hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact (outside_32330302 htau hs32330302).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy3233030 | hy3233030
                · have hs32330301 : InSquare (107/640) (233/640) (1/640) tau := by
                    convert childLR hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact Batch0476.cell3812.sound htau (by
                    simp only [Batch0476.cell3812, Batch0476.tau3812, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330301 (by positivity) using 1 <;> norm_num)
                · have hs32330303 : InSquare (107/640) (47/128) (1/640) tau := by
                    convert childUR hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact (outside_32330303 htau hs32330303).elim
            · have hs3233032 : InSquare (53/320) (119/320) (1/320) tau := by
                convert childUL hs323303 hx323303 hy323303 using 1 <;> norm_num
              exact (outside_3233032 htau hs3233032).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy323303 | hy323303
            · have hs3233031 : InSquare (11/64) (117/320) (1/320) tau := by
                convert childLR hs323303 hx323303 hy323303 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233031 | hx3233031
              · rcases le_total tau.im (117/320 : ℝ) with hy3233031 | hy3233031
                · have hs32330310 : InSquare (109/640) (233/640) (1/640) tau := by
                    convert childLL hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact Batch0476.cell3813.sound htau (by
                    simp only [Batch0476.cell3813, Batch0476.tau3813, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330310 (by positivity) using 1 <;> norm_num)
                · have hs32330312 : InSquare (109/640) (47/128) (1/640) tau := by
                    convert childUL hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330312 htau hs32330312).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy3233031 | hy3233031
                · have hs32330311 : InSquare (111/640) (233/640) (1/640) tau := by
                    convert childLR hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330311 htau hs32330311).elim
                · have hs32330313 : InSquare (111/640) (47/128) (1/640) tau := by
                    convert childUR hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330313 htau hs32330313).elim
            · have hs3233033 : InSquare (11/64) (119/320) (1/320) tau := by
                convert childUR hs323303 hx323303 hy323303 using 1 <;> norm_num
              exact (outside_3233033 htau hs3233033).elim
    · have hs32332 : InSquare (13/80) (31/80) (1/80) tau := by
        convert childUL hs hx3233 hy3233 using 1 <;> norm_num
      exact (outside_32332 htau hs32332).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3233 | hy3233
    · have hs32331 : InSquare (3/16) (29/80) (1/80) tau := by
        convert childLR hs hx3233 hy3233 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32331 | hx32331
      · rcases le_total tau.im (29/80 : ℝ) with hy32331 | hy32331
        · have hs323310 : InSquare (29/160) (57/160) (1/160) tau := by
            convert childLL hs32331 hx32331 hy32331 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323310 | hx323310
          · rcases le_total tau.im (57/160 : ℝ) with hy323310 | hy323310
            · have hs3233100 : InSquare (57/320) (113/320) (1/320) tau := by
                convert childLL hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx3233100 | hx3233100
              · rcases le_total tau.im (113/320 : ℝ) with hy3233100 | hy3233100
                · have hs32331000 : InSquare (113/640) (45/128) (1/640) tau := by
                    convert childLL hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0476.cell3814.sound htau (by
                    simp only [Batch0476.cell3814, Batch0476.tau3814, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331000 (by positivity) using 1 <;> norm_num)
                · have hs32331002 : InSquare (113/640) (227/640) (1/640) tau := by
                    convert childUL hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0477.cell3816.sound htau (by
                    simp only [Batch0477.cell3816, Batch0477.tau3816, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233100 | hy3233100
                · have hs32331001 : InSquare (23/128) (45/128) (1/640) tau := by
                    convert childLR hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0476.cell3815.sound htau (by
                    simp only [Batch0476.cell3815, Batch0476.tau3815, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331001 (by positivity) using 1 <;> norm_num)
                · have hs32331003 : InSquare (23/128) (227/640) (1/640) tau := by
                    convert childUR hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0477.cell3817.sound htau (by
                    simp only [Batch0477.cell3817, Batch0477.tau3817, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331003 (by positivity) using 1 <;> norm_num)
            · have hs3233102 : InSquare (57/320) (23/64) (1/320) tau := by
                convert childUL hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx3233102 | hx3233102
              · rcases le_total tau.im (23/64 : ℝ) with hy3233102 | hy3233102
                · have hs32331020 : InSquare (113/640) (229/640) (1/640) tau := by
                    convert childLL hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0477.cell3822.sound htau (by
                    simp only [Batch0477.cell3822, Batch0477.tau3822, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331020 (by positivity) using 1 <;> norm_num)
                · have hs32331022 : InSquare (113/640) (231/640) (1/640) tau := by
                    convert childUL hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0478.cell3824.sound htau (by
                    simp only [Batch0478.cell3824, Batch0478.tau3824, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233102 | hy3233102
                · have hs32331021 : InSquare (23/128) (229/640) (1/640) tau := by
                    convert childLR hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0477.cell3823.sound htau (by
                    simp only [Batch0477.cell3823, Batch0477.tau3823, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331021 (by positivity) using 1 <;> norm_num)
                · have hs32331023 : InSquare (23/128) (231/640) (1/640) tau := by
                    convert childUR hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact (outside_32331023 htau hs32331023).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy323310 | hy323310
            · have hs3233101 : InSquare (59/320) (113/320) (1/320) tau := by
                convert childLR hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx3233101 | hx3233101
              · rcases le_total tau.im (113/320 : ℝ) with hy3233101 | hy3233101
                · have hs32331010 : InSquare (117/640) (45/128) (1/640) tau := by
                    convert childLL hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3818.sound htau (by
                    simp only [Batch0477.cell3818, Batch0477.tau3818, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331010 (by positivity) using 1 <;> norm_num)
                · have hs32331012 : InSquare (117/640) (227/640) (1/640) tau := by
                    convert childUL hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3820.sound htau (by
                    simp only [Batch0477.cell3820, Batch0477.tau3820, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233101 | hy3233101
                · have hs32331011 : InSquare (119/640) (45/128) (1/640) tau := by
                    convert childLR hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3819.sound htau (by
                    simp only [Batch0477.cell3819, Batch0477.tau3819, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331011 (by positivity) using 1 <;> norm_num)
                · have hs32331013 : InSquare (119/640) (227/640) (1/640) tau := by
                    convert childUR hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3821.sound htau (by
                    simp only [Batch0477.cell3821, Batch0477.tau3821, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331013 (by positivity) using 1 <;> norm_num)
            · have hs3233103 : InSquare (59/320) (23/64) (1/320) tau := by
                convert childUR hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx3233103 | hx3233103
              · rcases le_total tau.im (23/64 : ℝ) with hy3233103 | hy3233103
                · have hs32331030 : InSquare (117/640) (229/640) (1/640) tau := by
                    convert childLL hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact Batch0478.cell3825.sound htau (by
                    simp only [Batch0478.cell3825, Batch0478.tau3825, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331030 (by positivity) using 1 <;> norm_num)
                · have hs32331032 : InSquare (117/640) (231/640) (1/640) tau := by
                    convert childUL hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331032 htau hs32331032).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy3233103 | hy3233103
                · have hs32331031 : InSquare (119/640) (229/640) (1/640) tau := by
                    convert childLR hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331031 htau hs32331031).elim
                · have hs32331033 : InSquare (119/640) (231/640) (1/640) tau := by
                    convert childUR hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331033 htau hs32331033).elim
        · have hs323312 : InSquare (29/160) (59/160) (1/160) tau := by
            convert childUL hs32331 hx32331 hy32331 using 1 <;> norm_num
          exact (outside_323312 htau hs323312).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy32331 | hy32331
        · have hs323311 : InSquare (31/160) (57/160) (1/160) tau := by
            convert childLR hs32331 hx32331 hy32331 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323311 | hx323311
          · rcases le_total tau.im (57/160 : ℝ) with hy323311 | hy323311
            · have hs3233110 : InSquare (61/320) (113/320) (1/320) tau := by
                convert childLL hs323311 hx323311 hy323311 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx3233110 | hx3233110
              · rcases le_total tau.im (113/320 : ℝ) with hy3233110 | hy3233110
                · have hs32331100 : InSquare (121/640) (45/128) (1/640) tau := by
                    convert childLL hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3826.sound htau (by
                    simp only [Batch0478.cell3826, Batch0478.tau3826, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331100 (by positivity) using 1 <;> norm_num)
                · have hs32331102 : InSquare (121/640) (227/640) (1/640) tau := by
                    convert childUL hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3828.sound htau (by
                    simp only [Batch0478.cell3828, Batch0478.tau3828, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233110 | hy3233110
                · have hs32331101 : InSquare (123/640) (45/128) (1/640) tau := by
                    convert childLR hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3827.sound htau (by
                    simp only [Batch0478.cell3827, Batch0478.tau3827, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331101 (by positivity) using 1 <;> norm_num)
                · have hs32331103 : InSquare (123/640) (227/640) (1/640) tau := by
                    convert childUR hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact (outside_32331103 htau hs32331103).elim
            · have hs3233112 : InSquare (61/320) (23/64) (1/320) tau := by
                convert childUL hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233112 htau hs3233112).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy323311 | hy323311
            · have hs3233111 : InSquare (63/320) (113/320) (1/320) tau := by
                convert childLR hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233111 htau hs3233111).elim
            · have hs3233113 : InSquare (63/320) (23/64) (1/320) tau := by
                convert childUR hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233113 htau hs3233113).elim
        · have hs323313 : InSquare (31/160) (59/160) (1/160) tau := by
            convert childUR hs32331 hx32331 hy32331 using 1 <;> norm_num
          exact (outside_323313 htau hs323313).elim
    · have hs32333 : InSquare (3/16) (31/80) (1/80) tau := by
        convert childUR hs hx3233 hy3233 using 1 <;> norm_num
      exact (outside_32333 htau hs32333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3300 | hx3300
  · rcases le_total tau.im (9/40 : ℝ) with hy3300 | hy3300
    · have hs33000 : InSquare (17/80) (17/80) (1/80) tau := by
        convert childLL hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33000 | hx33000
      · rcases le_total tau.im (17/80 : ℝ) with hy33000 | hy33000
        · have hs330000 : InSquare (33/160) (33/160) (1/160) tau := by
            convert childLL hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0143.cell1151.sound htau (by
            simp only [Batch0143.cell1151, Batch0143.tau1151, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330000 (by positivity) using 1 <;> norm_num)
        · have hs330002 : InSquare (33/160) (7/32) (1/160) tau := by
            convert childUL hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1153.sound htau (by
            simp only [Batch0144.cell1153, Batch0144.tau1153, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33000 | hy33000
        · have hs330001 : InSquare (7/32) (33/160) (1/160) tau := by
            convert childLR hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1152.sound htau (by
            simp only [Batch0144.cell1152, Batch0144.tau1152, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330001 (by positivity) using 1 <;> norm_num)
        · have hs330003 : InSquare (7/32) (7/32) (1/160) tau := by
            convert childUR hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1154.sound htau (by
            simp only [Batch0144.cell1154, Batch0144.tau1154, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330003 (by positivity) using 1 <;> norm_num)
    · have hs33002 : InSquare (17/80) (19/80) (1/80) tau := by
        convert childUL hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33002 | hx33002
      · rcases le_total tau.im (19/80 : ℝ) with hy33002 | hy33002
        · have hs330020 : InSquare (33/160) (37/160) (1/160) tau := by
            convert childLL hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0144.cell1159.sound htau (by
            simp only [Batch0144.cell1159, Batch0144.tau1159, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330020 (by positivity) using 1 <;> norm_num)
        · have hs330022 : InSquare (33/160) (39/160) (1/160) tau := by
            convert childUL hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1161.sound htau (by
            simp only [Batch0145.cell1161, Batch0145.tau1161, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33002 | hy33002
        · have hs330021 : InSquare (7/32) (37/160) (1/160) tau := by
            convert childLR hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1160.sound htau (by
            simp only [Batch0145.cell1160, Batch0145.tau1160, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330021 (by positivity) using 1 <;> norm_num)
        · have hs330023 : InSquare (7/32) (39/160) (1/160) tau := by
            convert childUR hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1162.sound htau (by
            simp only [Batch0145.cell1162, Batch0145.tau1162, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3300 | hy3300
    · have hs33001 : InSquare (19/80) (17/80) (1/80) tau := by
        convert childLR hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33001 | hx33001
      · rcases le_total tau.im (17/80 : ℝ) with hy33001 | hy33001
        · have hs330010 : InSquare (37/160) (33/160) (1/160) tau := by
            convert childLL hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1155.sound htau (by
            simp only [Batch0144.cell1155, Batch0144.tau1155, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330010 (by positivity) using 1 <;> norm_num)
        · have hs330012 : InSquare (37/160) (7/32) (1/160) tau := by
            convert childUL hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1157.sound htau (by
            simp only [Batch0144.cell1157, Batch0144.tau1157, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33001 | hy33001
        · have hs330011 : InSquare (39/160) (33/160) (1/160) tau := by
            convert childLR hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1156.sound htau (by
            simp only [Batch0144.cell1156, Batch0144.tau1156, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330011 (by positivity) using 1 <;> norm_num)
        · have hs330013 : InSquare (39/160) (7/32) (1/160) tau := by
            convert childUR hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1158.sound htau (by
            simp only [Batch0144.cell1158, Batch0144.tau1158, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330013 (by positivity) using 1 <;> norm_num)
    · have hs33003 : InSquare (19/80) (19/80) (1/80) tau := by
        convert childUR hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33003 | hx33003
      · rcases le_total tau.im (19/80 : ℝ) with hy33003 | hy33003
        · have hs330030 : InSquare (37/160) (37/160) (1/160) tau := by
            convert childLL hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1163.sound htau (by
            simp only [Batch0145.cell1163, Batch0145.tau1163, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330030 (by positivity) using 1 <;> norm_num)
        · have hs330032 : InSquare (37/160) (39/160) (1/160) tau := by
            convert childUL hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1165.sound htau (by
            simp only [Batch0145.cell1165, Batch0145.tau1165, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33003 | hy33003
        · have hs330031 : InSquare (39/160) (37/160) (1/160) tau := by
            convert childLR hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1164.sound htau (by
            simp only [Batch0145.cell1164, Batch0145.tau1164, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330031 (by positivity) using 1 <;> norm_num)
        · have hs330033 : InSquare (39/160) (39/160) (1/160) tau := by
            convert childUR hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1166.sound htau (by
            simp only [Batch0145.cell1166, Batch0145.tau1166, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3301 | hx3301
  · rcases le_total tau.im (9/40 : ℝ) with hy3301 | hy3301
    · have hs33010 : InSquare (21/80) (17/80) (1/80) tau := by
        convert childLL hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33010 | hx33010
      · rcases le_total tau.im (17/80 : ℝ) with hy33010 | hy33010
        · have hs330100 : InSquare (41/160) (33/160) (1/160) tau := by
            convert childLL hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0145.cell1167.sound htau (by
            simp only [Batch0145.cell1167, Batch0145.tau1167, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330100 (by positivity) using 1 <;> norm_num)
        · have hs330102 : InSquare (41/160) (7/32) (1/160) tau := by
            convert childUL hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1169.sound htau (by
            simp only [Batch0146.cell1169, Batch0146.tau1169, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33010 | hy33010
        · have hs330101 : InSquare (43/160) (33/160) (1/160) tau := by
            convert childLR hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1168.sound htau (by
            simp only [Batch0146.cell1168, Batch0146.tau1168, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330101 (by positivity) using 1 <;> norm_num)
        · have hs330103 : InSquare (43/160) (7/32) (1/160) tau := by
            convert childUR hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1170.sound htau (by
            simp only [Batch0146.cell1170, Batch0146.tau1170, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330103 (by positivity) using 1 <;> norm_num)
    · have hs33012 : InSquare (21/80) (19/80) (1/80) tau := by
        convert childUL hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33012 | hx33012
      · rcases le_total tau.im (19/80 : ℝ) with hy33012 | hy33012
        · have hs330120 : InSquare (41/160) (37/160) (1/160) tau := by
            convert childLL hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0146.cell1175.sound htau (by
            simp only [Batch0146.cell1175, Batch0146.tau1175, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330120 (by positivity) using 1 <;> norm_num)
        · have hs330122 : InSquare (41/160) (39/160) (1/160) tau := by
            convert childUL hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1177.sound htau (by
            simp only [Batch0147.cell1177, Batch0147.tau1177, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33012 | hy33012
        · have hs330121 : InSquare (43/160) (37/160) (1/160) tau := by
            convert childLR hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1176.sound htau (by
            simp only [Batch0147.cell1176, Batch0147.tau1176, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330121 (by positivity) using 1 <;> norm_num)
        · have hs330123 : InSquare (43/160) (39/160) (1/160) tau := by
            convert childUR hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1178.sound htau (by
            simp only [Batch0147.cell1178, Batch0147.tau1178, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3301 | hy3301
    · have hs33011 : InSquare (23/80) (17/80) (1/80) tau := by
        convert childLR hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33011 | hx33011
      · rcases le_total tau.im (17/80 : ℝ) with hy33011 | hy33011
        · have hs330110 : InSquare (9/32) (33/160) (1/160) tau := by
            convert childLL hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1171.sound htau (by
            simp only [Batch0146.cell1171, Batch0146.tau1171, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330110 (by positivity) using 1 <;> norm_num)
        · have hs330112 : InSquare (9/32) (7/32) (1/160) tau := by
            convert childUL hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1173.sound htau (by
            simp only [Batch0146.cell1173, Batch0146.tau1173, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33011 | hy33011
        · have hs330111 : InSquare (47/160) (33/160) (1/160) tau := by
            convert childLR hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1172.sound htau (by
            simp only [Batch0146.cell1172, Batch0146.tau1172, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330111 (by positivity) using 1 <;> norm_num)
        · have hs330113 : InSquare (47/160) (7/32) (1/160) tau := by
            convert childUR hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1174.sound htau (by
            simp only [Batch0146.cell1174, Batch0146.tau1174, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330113 (by positivity) using 1 <;> norm_num)
    · have hs33013 : InSquare (23/80) (19/80) (1/80) tau := by
        convert childUR hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33013 | hx33013
      · rcases le_total tau.im (19/80 : ℝ) with hy33013 | hy33013
        · have hs330130 : InSquare (9/32) (37/160) (1/160) tau := by
            convert childLL hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1179.sound htau (by
            simp only [Batch0147.cell1179, Batch0147.tau1179, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330130 (by positivity) using 1 <;> norm_num)
        · have hs330132 : InSquare (9/32) (39/160) (1/160) tau := by
            convert childUL hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1181.sound htau (by
            simp only [Batch0147.cell1181, Batch0147.tau1181, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33013 | hy33013
        · have hs330131 : InSquare (47/160) (37/160) (1/160) tau := by
            convert childLR hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1180.sound htau (by
            simp only [Batch0147.cell1180, Batch0147.tau1180, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330131 (by positivity) using 1 <;> norm_num)
        · have hs330133 : InSquare (47/160) (39/160) (1/160) tau := by
            convert childUR hs33013 hx33013 hy33013 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330133 | hx330133
          · rcases le_total tau.im (39/160 : ℝ) with hy330133 | hy330133
            · have hs3301330 : InSquare (93/320) (77/320) (1/320) tau := by
                convert childLL hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2420.sound htau (by
                simp only [Batch0302.cell2420, Batch0302.tau2420, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301330 (by positivity) using 1 <;> norm_num)
            · have hs3301332 : InSquare (93/320) (79/320) (1/320) tau := by
                convert childUL hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2422.sound htau (by
                simp only [Batch0302.cell2422, Batch0302.tau2422, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy330133 | hy330133
            · have hs3301331 : InSquare (19/64) (77/320) (1/320) tau := by
                convert childLR hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2421.sound htau (by
                simp only [Batch0302.cell2421, Batch0302.tau2421, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301331 (by positivity) using 1 <;> norm_num)
            · have hs3301333 : InSquare (19/64) (79/320) (1/320) tau := by
                convert childUR hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2423.sound htau (by
                simp only [Batch0302.cell2423, Batch0302.tau2423, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3302 | hx3302
  · rcases le_total tau.im (11/40 : ℝ) with hy3302 | hy3302
    · have hs33020 : InSquare (17/80) (21/80) (1/80) tau := by
        convert childLL hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33020 | hx33020
      · rcases le_total tau.im (21/80 : ℝ) with hy33020 | hy33020
        · have hs330200 : InSquare (33/160) (41/160) (1/160) tau := by
            convert childLL hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0147.cell1182.sound htau (by
            simp only [Batch0147.cell1182, Batch0147.tau1182, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330200 (by positivity) using 1 <;> norm_num)
        · have hs330202 : InSquare (33/160) (43/160) (1/160) tau := by
            convert childUL hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0148.cell1184.sound htau (by
            simp only [Batch0148.cell1184, Batch0148.tau1184, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33020 | hy33020
        · have hs330201 : InSquare (7/32) (41/160) (1/160) tau := by
            convert childLR hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0147.cell1183.sound htau (by
            simp only [Batch0147.cell1183, Batch0147.tau1183, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330201 (by positivity) using 1 <;> norm_num)
        · have hs330203 : InSquare (7/32) (43/160) (1/160) tau := by
            convert childUR hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0148.cell1185.sound htau (by
            simp only [Batch0148.cell1185, Batch0148.tau1185, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330203 (by positivity) using 1 <;> norm_num)
    · have hs33022 : InSquare (17/80) (23/80) (1/80) tau := by
        convert childUL hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33022 | hx33022
      · rcases le_total tau.im (23/80 : ℝ) with hy33022 | hy33022
        · have hs330220 : InSquare (33/160) (9/32) (1/160) tau := by
            convert childLL hs33022 hx33022 hy33022 using 1 <;> norm_num
          exact Batch0148.cell1190.sound htau (by
            simp only [Batch0148.cell1190, Batch0148.tau1190, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330220 (by positivity) using 1 <;> norm_num)
        · have hs330222 : InSquare (33/160) (47/160) (1/160) tau := by
            convert childUL hs33022 hx33022 hy33022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx330222 | hx330222
          · rcases le_total tau.im (47/160 : ℝ) with hy330222 | hy330222
            · have hs3302220 : InSquare (13/64) (93/320) (1/320) tau := by
                convert childLL hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2424.sound htau (by
                simp only [Batch0303.cell2424, Batch0303.tau2424, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302220 (by positivity) using 1 <;> norm_num)
            · have hs3302222 : InSquare (13/64) (19/64) (1/320) tau := by
                convert childUL hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2426.sound htau (by
                simp only [Batch0303.cell2426, Batch0303.tau2426, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330222 | hy330222
            · have hs3302221 : InSquare (67/320) (93/320) (1/320) tau := by
                convert childLR hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2425.sound htau (by
                simp only [Batch0303.cell2425, Batch0303.tau2425, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302221 (by positivity) using 1 <;> norm_num)
            · have hs3302223 : InSquare (67/320) (19/64) (1/320) tau := by
                convert childUR hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2427.sound htau (by
                simp only [Batch0303.cell2427, Batch0303.tau2427, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33022 | hy33022
        · have hs330221 : InSquare (7/32) (9/32) (1/160) tau := by
            convert childLR hs33022 hx33022 hy33022 using 1 <;> norm_num
          exact Batch0148.cell1191.sound htau (by
            simp only [Batch0148.cell1191, Batch0148.tau1191, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330221 (by positivity) using 1 <;> norm_num)
        · have hs330223 : InSquare (7/32) (47/160) (1/160) tau := by
            convert childUR hs33022 hx33022 hy33022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx330223 | hx330223
          · rcases le_total tau.im (47/160 : ℝ) with hy330223 | hy330223
            · have hs3302230 : InSquare (69/320) (93/320) (1/320) tau := by
                convert childLL hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2428.sound htau (by
                simp only [Batch0303.cell2428, Batch0303.tau2428, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302230 (by positivity) using 1 <;> norm_num)
            · have hs3302232 : InSquare (69/320) (19/64) (1/320) tau := by
                convert childUL hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2430.sound htau (by
                simp only [Batch0303.cell2430, Batch0303.tau2430, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330223 | hy330223
            · have hs3302231 : InSquare (71/320) (93/320) (1/320) tau := by
                convert childLR hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2429.sound htau (by
                simp only [Batch0303.cell2429, Batch0303.tau2429, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302231 (by positivity) using 1 <;> norm_num)
            · have hs3302233 : InSquare (71/320) (19/64) (1/320) tau := by
                convert childUR hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2431.sound htau (by
                simp only [Batch0303.cell2431, Batch0303.tau2431, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3302 | hy3302
    · have hs33021 : InSquare (19/80) (21/80) (1/80) tau := by
        convert childLR hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33021 | hx33021
      · rcases le_total tau.im (21/80 : ℝ) with hy33021 | hy33021
        · have hs330210 : InSquare (37/160) (41/160) (1/160) tau := by
            convert childLL hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1186.sound htau (by
            simp only [Batch0148.cell1186, Batch0148.tau1186, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330210 (by positivity) using 1 <;> norm_num)
        · have hs330212 : InSquare (37/160) (43/160) (1/160) tau := by
            convert childUL hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1188.sound htau (by
            simp only [Batch0148.cell1188, Batch0148.tau1188, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33021 | hy33021
        · have hs330211 : InSquare (39/160) (41/160) (1/160) tau := by
            convert childLR hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1187.sound htau (by
            simp only [Batch0148.cell1187, Batch0148.tau1187, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330211 (by positivity) using 1 <;> norm_num)
        · have hs330213 : InSquare (39/160) (43/160) (1/160) tau := by
            convert childUR hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1189.sound htau (by
            simp only [Batch0148.cell1189, Batch0148.tau1189, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330213 (by positivity) using 1 <;> norm_num)
    · have hs33023 : InSquare (19/80) (23/80) (1/80) tau := by
        convert childUR hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33023 | hx33023
      · rcases le_total tau.im (23/80 : ℝ) with hy33023 | hy33023
        · have hs330230 : InSquare (37/160) (9/32) (1/160) tau := by
            convert childLL hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx330230 | hx330230
          · rcases le_total tau.im (9/32 : ℝ) with hy330230 | hy330230
            · have hs3302300 : InSquare (73/320) (89/320) (1/320) tau := by
                convert childLL hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2432.sound htau (by
                simp only [Batch0304.cell2432, Batch0304.tau2432, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302300 (by positivity) using 1 <;> norm_num)
            · have hs3302302 : InSquare (73/320) (91/320) (1/320) tau := by
                convert childUL hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2434.sound htau (by
                simp only [Batch0304.cell2434, Batch0304.tau2434, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330230 | hy330230
            · have hs3302301 : InSquare (15/64) (89/320) (1/320) tau := by
                convert childLR hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2433.sound htau (by
                simp only [Batch0304.cell2433, Batch0304.tau2433, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302301 (by positivity) using 1 <;> norm_num)
            · have hs3302303 : InSquare (15/64) (91/320) (1/320) tau := by
                convert childUR hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2435.sound htau (by
                simp only [Batch0304.cell2435, Batch0304.tau2435, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302303 (by positivity) using 1 <;> norm_num)
        · have hs330232 : InSquare (37/160) (47/160) (1/160) tau := by
            convert childUL hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx330232 | hx330232
          · rcases le_total tau.im (47/160 : ℝ) with hy330232 | hy330232
            · have hs3302320 : InSquare (73/320) (93/320) (1/320) tau := by
                convert childLL hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2440.sound htau (by
                simp only [Batch0305.cell2440, Batch0305.tau2440, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302320 (by positivity) using 1 <;> norm_num)
            · have hs3302322 : InSquare (73/320) (19/64) (1/320) tau := by
                convert childUL hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2442.sound htau (by
                simp only [Batch0305.cell2442, Batch0305.tau2442, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330232 | hy330232
            · have hs3302321 : InSquare (15/64) (93/320) (1/320) tau := by
                convert childLR hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2441.sound htau (by
                simp only [Batch0305.cell2441, Batch0305.tau2441, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302321 (by positivity) using 1 <;> norm_num)
            · have hs3302323 : InSquare (15/64) (19/64) (1/320) tau := by
                convert childUR hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2443.sound htau (by
                simp only [Batch0305.cell2443, Batch0305.tau2443, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33023 | hy33023
        · have hs330231 : InSquare (39/160) (9/32) (1/160) tau := by
            convert childLR hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx330231 | hx330231
          · rcases le_total tau.im (9/32 : ℝ) with hy330231 | hy330231
            · have hs3302310 : InSquare (77/320) (89/320) (1/320) tau := by
                convert childLL hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2436.sound htau (by
                simp only [Batch0304.cell2436, Batch0304.tau2436, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302310 (by positivity) using 1 <;> norm_num)
            · have hs3302312 : InSquare (77/320) (91/320) (1/320) tau := by
                convert childUL hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2438.sound htau (by
                simp only [Batch0304.cell2438, Batch0304.tau2438, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330231 | hy330231
            · have hs3302311 : InSquare (79/320) (89/320) (1/320) tau := by
                convert childLR hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2437.sound htau (by
                simp only [Batch0304.cell2437, Batch0304.tau2437, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302311 (by positivity) using 1 <;> norm_num)
            · have hs3302313 : InSquare (79/320) (91/320) (1/320) tau := by
                convert childUR hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2439.sound htau (by
                simp only [Batch0304.cell2439, Batch0304.tau2439, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302313 (by positivity) using 1 <;> norm_num)
        · have hs330233 : InSquare (39/160) (47/160) (1/160) tau := by
            convert childUR hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx330233 | hx330233
          · rcases le_total tau.im (47/160 : ℝ) with hy330233 | hy330233
            · have hs3302330 : InSquare (77/320) (93/320) (1/320) tau := by
                convert childLL hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2444.sound htau (by
                simp only [Batch0305.cell2444, Batch0305.tau2444, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302330 (by positivity) using 1 <;> norm_num)
            · have hs3302332 : InSquare (77/320) (19/64) (1/320) tau := by
                convert childUL hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2446.sound htau (by
                simp only [Batch0305.cell2446, Batch0305.tau2446, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330233 | hy330233
            · have hs3302331 : InSquare (79/320) (93/320) (1/320) tau := by
                convert childLR hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2445.sound htau (by
                simp only [Batch0305.cell2445, Batch0305.tau2445, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302331 (by positivity) using 1 <;> norm_num)
            · have hs3302333 : InSquare (79/320) (19/64) (1/320) tau := by
                convert childUR hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2447.sound htau (by
                simp only [Batch0305.cell2447, Batch0305.tau2447, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_330333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/160) (47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (93/320) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3303 | hx3303
  · rcases le_total tau.im (11/40 : ℝ) with hy3303 | hy3303
    · have hs33030 : InSquare (21/80) (21/80) (1/80) tau := by
        convert childLL hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33030 | hx33030
      · rcases le_total tau.im (21/80 : ℝ) with hy33030 | hy33030
        · have hs330300 : InSquare (41/160) (41/160) (1/160) tau := by
            convert childLL hs33030 hx33030 hy33030 using 1 <;> norm_num
          exact Batch0149.cell1192.sound htau (by
            simp only [Batch0149.cell1192, Batch0149.tau1192, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330300 (by positivity) using 1 <;> norm_num)
        · have hs330302 : InSquare (41/160) (43/160) (1/160) tau := by
            convert childUL hs33030 hx33030 hy33030 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330302 | hx330302
          · rcases le_total tau.im (43/160 : ℝ) with hy330302 | hy330302
            · have hs3303020 : InSquare (81/320) (17/64) (1/320) tau := by
                convert childLL hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2448.sound htau (by
                simp only [Batch0306.cell2448, Batch0306.tau2448, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303020 (by positivity) using 1 <;> norm_num)
            · have hs3303022 : InSquare (81/320) (87/320) (1/320) tau := by
                convert childUL hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2450.sound htau (by
                simp only [Batch0306.cell2450, Batch0306.tau2450, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330302 | hy330302
            · have hs3303021 : InSquare (83/320) (17/64) (1/320) tau := by
                convert childLR hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2449.sound htau (by
                simp only [Batch0306.cell2449, Batch0306.tau2449, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303021 (by positivity) using 1 <;> norm_num)
            · have hs3303023 : InSquare (83/320) (87/320) (1/320) tau := by
                convert childUR hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2451.sound htau (by
                simp only [Batch0306.cell2451, Batch0306.tau2451, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33030 | hy33030
        · have hs330301 : InSquare (43/160) (41/160) (1/160) tau := by
            convert childLR hs33030 hx33030 hy33030 using 1 <;> norm_num
          exact Batch0149.cell1193.sound htau (by
            simp only [Batch0149.cell1193, Batch0149.tau1193, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330301 (by positivity) using 1 <;> norm_num)
        · have hs330303 : InSquare (43/160) (43/160) (1/160) tau := by
            convert childUR hs33030 hx33030 hy33030 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330303 | hx330303
          · rcases le_total tau.im (43/160 : ℝ) with hy330303 | hy330303
            · have hs3303030 : InSquare (17/64) (17/64) (1/320) tau := by
                convert childLL hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2452.sound htau (by
                simp only [Batch0306.cell2452, Batch0306.tau2452, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303030 (by positivity) using 1 <;> norm_num)
            · have hs3303032 : InSquare (17/64) (87/320) (1/320) tau := by
                convert childUL hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2454.sound htau (by
                simp only [Batch0306.cell2454, Batch0306.tau2454, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330303 | hy330303
            · have hs3303031 : InSquare (87/320) (17/64) (1/320) tau := by
                convert childLR hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2453.sound htau (by
                simp only [Batch0306.cell2453, Batch0306.tau2453, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303031 (by positivity) using 1 <;> norm_num)
            · have hs3303033 : InSquare (87/320) (87/320) (1/320) tau := by
                convert childUR hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2455.sound htau (by
                simp only [Batch0306.cell2455, Batch0306.tau2455, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303033 (by positivity) using 1 <;> norm_num)
    · have hs33032 : InSquare (21/80) (23/80) (1/80) tau := by
        convert childUL hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33032 | hx33032
      · rcases le_total tau.im (23/80 : ℝ) with hy33032 | hy33032
        · have hs330320 : InSquare (41/160) (9/32) (1/160) tau := by
            convert childLL hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330320 | hx330320
          · rcases le_total tau.im (9/32 : ℝ) with hy330320 | hy330320
            · have hs3303200 : InSquare (81/320) (89/320) (1/320) tau := by
                convert childLL hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2472.sound htau (by
                simp only [Batch0309.cell2472, Batch0309.tau2472, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303200 (by positivity) using 1 <;> norm_num)
            · have hs3303202 : InSquare (81/320) (91/320) (1/320) tau := by
                convert childUL hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2474.sound htau (by
                simp only [Batch0309.cell2474, Batch0309.tau2474, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330320 | hy330320
            · have hs3303201 : InSquare (83/320) (89/320) (1/320) tau := by
                convert childLR hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2473.sound htau (by
                simp only [Batch0309.cell2473, Batch0309.tau2473, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303201 (by positivity) using 1 <;> norm_num)
            · have hs3303203 : InSquare (83/320) (91/320) (1/320) tau := by
                convert childUR hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2475.sound htau (by
                simp only [Batch0309.cell2475, Batch0309.tau2475, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303203 (by positivity) using 1 <;> norm_num)
        · have hs330322 : InSquare (41/160) (47/160) (1/160) tau := by
            convert childUL hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330322 | hx330322
          · rcases le_total tau.im (47/160 : ℝ) with hy330322 | hy330322
            · have hs3303220 : InSquare (81/320) (93/320) (1/320) tau := by
                convert childLL hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2480.sound htau (by
                simp only [Batch0310.cell2480, Batch0310.tau2480, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303220 (by positivity) using 1 <;> norm_num)
            · have hs3303222 : InSquare (81/320) (19/64) (1/320) tau := by
                convert childUL hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2482.sound htau (by
                simp only [Batch0310.cell2482, Batch0310.tau2482, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330322 | hy330322
            · have hs3303221 : InSquare (83/320) (93/320) (1/320) tau := by
                convert childLR hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2481.sound htau (by
                simp only [Batch0310.cell2481, Batch0310.tau2481, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303221 (by positivity) using 1 <;> norm_num)
            · have hs3303223 : InSquare (83/320) (19/64) (1/320) tau := by
                convert childUR hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2483.sound htau (by
                simp only [Batch0310.cell2483, Batch0310.tau2483, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33032 | hy33032
        · have hs330321 : InSquare (43/160) (9/32) (1/160) tau := by
            convert childLR hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330321 | hx330321
          · rcases le_total tau.im (9/32 : ℝ) with hy330321 | hy330321
            · have hs3303210 : InSquare (17/64) (89/320) (1/320) tau := by
                convert childLL hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2476.sound htau (by
                simp only [Batch0309.cell2476, Batch0309.tau2476, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303210 (by positivity) using 1 <;> norm_num)
            · have hs3303212 : InSquare (17/64) (91/320) (1/320) tau := by
                convert childUL hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2478.sound htau (by
                simp only [Batch0309.cell2478, Batch0309.tau2478, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330321 | hy330321
            · have hs3303211 : InSquare (87/320) (89/320) (1/320) tau := by
                convert childLR hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2477.sound htau (by
                simp only [Batch0309.cell2477, Batch0309.tau2477, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303211 (by positivity) using 1 <;> norm_num)
            · have hs3303213 : InSquare (87/320) (91/320) (1/320) tau := by
                convert childUR hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2479.sound htau (by
                simp only [Batch0309.cell2479, Batch0309.tau2479, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303213 (by positivity) using 1 <;> norm_num)
        · have hs330323 : InSquare (43/160) (47/160) (1/160) tau := by
            convert childUR hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330323 | hx330323
          · rcases le_total tau.im (47/160 : ℝ) with hy330323 | hy330323
            · have hs3303230 : InSquare (17/64) (93/320) (1/320) tau := by
                convert childLL hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2484.sound htau (by
                simp only [Batch0310.cell2484, Batch0310.tau2484, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303230 (by positivity) using 1 <;> norm_num)
            · have hs3303232 : InSquare (17/64) (19/64) (1/320) tau := by
                convert childUL hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2486.sound htau (by
                simp only [Batch0310.cell2486, Batch0310.tau2486, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330323 | hy330323
            · have hs3303231 : InSquare (87/320) (93/320) (1/320) tau := by
                convert childLR hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2485.sound htau (by
                simp only [Batch0310.cell2485, Batch0310.tau2485, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303231 (by positivity) using 1 <;> norm_num)
            · have hs3303233 : InSquare (87/320) (19/64) (1/320) tau := by
                convert childUR hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2487.sound htau (by
                simp only [Batch0310.cell2487, Batch0310.tau2487, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3303 | hy3303
    · have hs33031 : InSquare (23/80) (21/80) (1/80) tau := by
        convert childLR hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33031 | hx33031
      · rcases le_total tau.im (21/80 : ℝ) with hy33031 | hy33031
        · have hs330310 : InSquare (9/32) (41/160) (1/160) tau := by
            convert childLL hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330310 | hx330310
          · rcases le_total tau.im (41/160 : ℝ) with hy330310 | hy330310
            · have hs3303100 : InSquare (89/320) (81/320) (1/320) tau := by
                convert childLL hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2456.sound htau (by
                simp only [Batch0307.cell2456, Batch0307.tau2456, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303100 (by positivity) using 1 <;> norm_num)
            · have hs3303102 : InSquare (89/320) (83/320) (1/320) tau := by
                convert childUL hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2458.sound htau (by
                simp only [Batch0307.cell2458, Batch0307.tau2458, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy330310 | hy330310
            · have hs3303101 : InSquare (91/320) (81/320) (1/320) tau := by
                convert childLR hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2457.sound htau (by
                simp only [Batch0307.cell2457, Batch0307.tau2457, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303101 (by positivity) using 1 <;> norm_num)
            · have hs3303103 : InSquare (91/320) (83/320) (1/320) tau := by
                convert childUR hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2459.sound htau (by
                simp only [Batch0307.cell2459, Batch0307.tau2459, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303103 (by positivity) using 1 <;> norm_num)
        · have hs330312 : InSquare (9/32) (43/160) (1/160) tau := by
            convert childUL hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330312 | hx330312
          · rcases le_total tau.im (43/160 : ℝ) with hy330312 | hy330312
            · have hs3303120 : InSquare (89/320) (17/64) (1/320) tau := by
                convert childLL hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2464.sound htau (by
                simp only [Batch0308.cell2464, Batch0308.tau2464, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303120 (by positivity) using 1 <;> norm_num)
            · have hs3303122 : InSquare (89/320) (87/320) (1/320) tau := by
                convert childUL hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2466.sound htau (by
                simp only [Batch0308.cell2466, Batch0308.tau2466, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330312 | hy330312
            · have hs3303121 : InSquare (91/320) (17/64) (1/320) tau := by
                convert childLR hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2465.sound htau (by
                simp only [Batch0308.cell2465, Batch0308.tau2465, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303121 (by positivity) using 1 <;> norm_num)
            · have hs3303123 : InSquare (91/320) (87/320) (1/320) tau := by
                convert childUR hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2467.sound htau (by
                simp only [Batch0308.cell2467, Batch0308.tau2467, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33031 | hy33031
        · have hs330311 : InSquare (47/160) (41/160) (1/160) tau := by
            convert childLR hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330311 | hx330311
          · rcases le_total tau.im (41/160 : ℝ) with hy330311 | hy330311
            · have hs3303110 : InSquare (93/320) (81/320) (1/320) tau := by
                convert childLL hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2460.sound htau (by
                simp only [Batch0307.cell2460, Batch0307.tau2460, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303110 (by positivity) using 1 <;> norm_num)
            · have hs3303112 : InSquare (93/320) (83/320) (1/320) tau := by
                convert childUL hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2462.sound htau (by
                simp only [Batch0307.cell2462, Batch0307.tau2462, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy330311 | hy330311
            · have hs3303111 : InSquare (19/64) (81/320) (1/320) tau := by
                convert childLR hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2461.sound htau (by
                simp only [Batch0307.cell2461, Batch0307.tau2461, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303111 (by positivity) using 1 <;> norm_num)
            · have hs3303113 : InSquare (19/64) (83/320) (1/320) tau := by
                convert childUR hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2463.sound htau (by
                simp only [Batch0307.cell2463, Batch0307.tau2463, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303113 (by positivity) using 1 <;> norm_num)
        · have hs330313 : InSquare (47/160) (43/160) (1/160) tau := by
            convert childUR hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330313 | hx330313
          · rcases le_total tau.im (43/160 : ℝ) with hy330313 | hy330313
            · have hs3303130 : InSquare (93/320) (17/64) (1/320) tau := by
                convert childLL hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2468.sound htau (by
                simp only [Batch0308.cell2468, Batch0308.tau2468, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303130 (by positivity) using 1 <;> norm_num)
            · have hs3303132 : InSquare (93/320) (87/320) (1/320) tau := by
                convert childUL hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2470.sound htau (by
                simp only [Batch0308.cell2470, Batch0308.tau2470, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330313 | hy330313
            · have hs3303131 : InSquare (19/64) (17/64) (1/320) tau := by
                convert childLR hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2469.sound htau (by
                simp only [Batch0308.cell2469, Batch0308.tau2469, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303131 (by positivity) using 1 <;> norm_num)
            · have hs3303133 : InSquare (19/64) (87/320) (1/320) tau := by
                convert childUR hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2471.sound htau (by
                simp only [Batch0308.cell2471, Batch0308.tau2471, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303133 (by positivity) using 1 <;> norm_num)
    · have hs33033 : InSquare (23/80) (23/80) (1/80) tau := by
        convert childUR hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33033 | hx33033
      · rcases le_total tau.im (23/80 : ℝ) with hy33033 | hy33033
        · have hs330330 : InSquare (9/32) (9/32) (1/160) tau := by
            convert childLL hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330330 | hx330330
          · rcases le_total tau.im (9/32 : ℝ) with hy330330 | hy330330
            · have hs3303300 : InSquare (89/320) (89/320) (1/320) tau := by
                convert childLL hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2488.sound htau (by
                simp only [Batch0311.cell2488, Batch0311.tau2488, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303300 (by positivity) using 1 <;> norm_num)
            · have hs3303302 : InSquare (89/320) (91/320) (1/320) tau := by
                convert childUL hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2490.sound htau (by
                simp only [Batch0311.cell2490, Batch0311.tau2490, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330330 | hy330330
            · have hs3303301 : InSquare (91/320) (89/320) (1/320) tau := by
                convert childLR hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2489.sound htau (by
                simp only [Batch0311.cell2489, Batch0311.tau2489, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303301 (by positivity) using 1 <;> norm_num)
            · have hs3303303 : InSquare (91/320) (91/320) (1/320) tau := by
                convert childUR hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2491.sound htau (by
                simp only [Batch0311.cell2491, Batch0311.tau2491, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303303 (by positivity) using 1 <;> norm_num)
        · have hs330332 : InSquare (9/32) (47/160) (1/160) tau := by
            convert childUL hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330332 | hx330332
          · rcases le_total tau.im (47/160 : ℝ) with hy330332 | hy330332
            · have hs3303320 : InSquare (89/320) (93/320) (1/320) tau := by
                convert childLL hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact Batch0311.cell2493.sound htau (by
                simp only [Batch0311.cell2493, Batch0311.tau2493, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303320 (by positivity) using 1 <;> norm_num)
            · have hs3303322 : InSquare (89/320) (19/64) (1/320) tau := by
                convert childUL hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303322 htau hs3303322).elim
          · rcases le_total tau.im (47/160 : ℝ) with hy330332 | hy330332
            · have hs3303321 : InSquare (91/320) (93/320) (1/320) tau := by
                convert childLR hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303321 htau hs3303321).elim
            · have hs3303323 : InSquare (91/320) (19/64) (1/320) tau := by
                convert childUR hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303323 htau hs3303323).elim
      · rcases le_total tau.im (23/80 : ℝ) with hy33033 | hy33033
        · have hs330331 : InSquare (47/160) (9/32) (1/160) tau := by
            convert childLR hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330331 | hx330331
          · rcases le_total tau.im (9/32 : ℝ) with hy330331 | hy330331
            · have hs3303310 : InSquare (93/320) (89/320) (1/320) tau := by
                convert childLL hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact Batch0311.cell2492.sound htau (by
                simp only [Batch0311.cell2492, Batch0311.tau2492, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303310 (by positivity) using 1 <;> norm_num)
            · have hs3303312 : InSquare (93/320) (91/320) (1/320) tau := by
                convert childUL hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303312 htau hs3303312).elim
          · rcases le_total tau.im (9/32 : ℝ) with hy330331 | hy330331
            · have hs3303311 : InSquare (19/64) (89/320) (1/320) tau := by
                convert childLR hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303311 htau hs3303311).elim
            · have hs3303313 : InSquare (19/64) (91/320) (1/320) tau := by
                convert childUR hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303313 htau hs3303313).elim
        · have hs330333 : InSquare (47/160) (47/160) (1/160) tau := by
            convert childUR hs33033 hx33033 hy33033 using 1 <;> norm_num
          exact (outside_330333 htau hs330333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_331031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/160) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (103/320) (79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3310 | hx3310
  · rcases le_total tau.im (9/40 : ℝ) with hy3310 | hy3310
    · have hs33100 : InSquare (5/16) (17/80) (1/80) tau := by
        convert childLL hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33100 | hx33100
      · rcases le_total tau.im (17/80 : ℝ) with hy33100 | hy33100
        · have hs331000 : InSquare (49/160) (33/160) (1/160) tau := by
            convert childLL hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1194.sound htau (by
            simp only [Batch0149.cell1194, Batch0149.tau1194, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331000 (by positivity) using 1 <;> norm_num)
        · have hs331002 : InSquare (49/160) (7/32) (1/160) tau := by
            convert childUL hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1196.sound htau (by
            simp only [Batch0149.cell1196, Batch0149.tau1196, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33100 | hy33100
        · have hs331001 : InSquare (51/160) (33/160) (1/160) tau := by
            convert childLR hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1195.sound htau (by
            simp only [Batch0149.cell1195, Batch0149.tau1195, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331001 (by positivity) using 1 <;> norm_num)
        · have hs331003 : InSquare (51/160) (7/32) (1/160) tau := by
            convert childUR hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1197.sound htau (by
            simp only [Batch0149.cell1197, Batch0149.tau1197, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331003 (by positivity) using 1 <;> norm_num)
    · have hs33102 : InSquare (5/16) (19/80) (1/80) tau := by
        convert childUL hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33102 | hx33102
      · rcases le_total tau.im (19/80 : ℝ) with hy33102 | hy33102
        · have hs331020 : InSquare (49/160) (37/160) (1/160) tau := by
            convert childLL hs33102 hx33102 hy33102 using 1 <;> norm_num
          exact Batch0149.cell1199.sound htau (by
            simp only [Batch0149.cell1199, Batch0149.tau1199, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331020 (by positivity) using 1 <;> norm_num)
        · have hs331022 : InSquare (49/160) (39/160) (1/160) tau := by
            convert childUL hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331022 | hx331022
          · rcases le_total tau.im (39/160 : ℝ) with hy331022 | hy331022
            · have hs3310220 : InSquare (97/320) (77/320) (1/320) tau := by
                convert childLL hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2506.sound htau (by
                simp only [Batch0313.cell2506, Batch0313.tau2506, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310220 (by positivity) using 1 <;> norm_num)
            · have hs3310222 : InSquare (97/320) (79/320) (1/320) tau := by
                convert childUL hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2508.sound htau (by
                simp only [Batch0313.cell2508, Batch0313.tau2508, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy331022 | hy331022
            · have hs3310221 : InSquare (99/320) (77/320) (1/320) tau := by
                convert childLR hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2507.sound htau (by
                simp only [Batch0313.cell2507, Batch0313.tau2507, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310221 (by positivity) using 1 <;> norm_num)
            · have hs3310223 : InSquare (99/320) (79/320) (1/320) tau := by
                convert childUR hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2509.sound htau (by
                simp only [Batch0313.cell2509, Batch0313.tau2509, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33102 | hy33102
        · have hs331021 : InSquare (51/160) (37/160) (1/160) tau := by
            convert childLR hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx331021 | hx331021
          · rcases le_total tau.im (37/160 : ℝ) with hy331021 | hy331021
            · have hs3310210 : InSquare (101/320) (73/320) (1/320) tau := by
                convert childLL hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0312.cell2502.sound htau (by
                simp only [Batch0312.cell2502, Batch0312.tau2502, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310210 (by positivity) using 1 <;> norm_num)
            · have hs3310212 : InSquare (101/320) (15/64) (1/320) tau := by
                convert childUL hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0313.cell2504.sound htau (by
                simp only [Batch0313.cell2504, Batch0313.tau2504, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy331021 | hy331021
            · have hs3310211 : InSquare (103/320) (73/320) (1/320) tau := by
                convert childLR hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0312.cell2503.sound htau (by
                simp only [Batch0312.cell2503, Batch0312.tau2503, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310211 (by positivity) using 1 <;> norm_num)
            · have hs3310213 : InSquare (103/320) (15/64) (1/320) tau := by
                convert childUR hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0313.cell2505.sound htau (by
                simp only [Batch0313.cell2505, Batch0313.tau2505, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310213 (by positivity) using 1 <;> norm_num)
        · have hs331023 : InSquare (51/160) (39/160) (1/160) tau := by
            convert childUR hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx331023 | hx331023
          · rcases le_total tau.im (39/160 : ℝ) with hy331023 | hy331023
            · have hs3310230 : InSquare (101/320) (77/320) (1/320) tau := by
                convert childLL hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0313.cell2510.sound htau (by
                simp only [Batch0313.cell2510, Batch0313.tau2510, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310230 (by positivity) using 1 <;> norm_num)
            · have hs3310232 : InSquare (101/320) (79/320) (1/320) tau := by
                convert childUL hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0314.cell2512.sound htau (by
                simp only [Batch0314.cell2512, Batch0314.tau2512, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy331023 | hy331023
            · have hs3310231 : InSquare (103/320) (77/320) (1/320) tau := by
                convert childLR hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0313.cell2511.sound htau (by
                simp only [Batch0313.cell2511, Batch0313.tau2511, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310231 (by positivity) using 1 <;> norm_num)
            · have hs3310233 : InSquare (103/320) (79/320) (1/320) tau := by
                convert childUR hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact (outside_3310233 htau hs3310233).elim
  · rcases le_total tau.im (9/40 : ℝ) with hy3310 | hy3310
    · have hs33101 : InSquare (27/80) (17/80) (1/80) tau := by
        convert childLR hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx33101 | hx33101
      · rcases le_total tau.im (17/80 : ℝ) with hy33101 | hy33101
        · have hs331010 : InSquare (53/160) (33/160) (1/160) tau := by
            convert childLL hs33101 hx33101 hy33101 using 1 <;> norm_num
          exact Batch0149.cell1198.sound htau (by
            simp only [Batch0149.cell1198, Batch0149.tau1198, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331010 (by positivity) using 1 <;> norm_num)
        · have hs331012 : InSquare (53/160) (7/32) (1/160) tau := by
            convert childUL hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx331012 | hx331012
          · rcases le_total tau.im (7/32 : ℝ) with hy331012 | hy331012
            · have hs3310120 : InSquare (21/64) (69/320) (1/320) tau := by
                convert childLL hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2497.sound htau (by
                simp only [Batch0312.cell2497, Batch0312.tau2497, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310120 (by positivity) using 1 <;> norm_num)
            · have hs3310122 : InSquare (21/64) (71/320) (1/320) tau := by
                convert childUL hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2499.sound htau (by
                simp only [Batch0312.cell2499, Batch0312.tau2499, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (7/32 : ℝ) with hy331012 | hy331012
            · have hs3310121 : InSquare (107/320) (69/320) (1/320) tau := by
                convert childLR hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2498.sound htau (by
                simp only [Batch0312.cell2498, Batch0312.tau2498, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310121 (by positivity) using 1 <;> norm_num)
            · have hs3310123 : InSquare (107/320) (71/320) (1/320) tau := by
                convert childUR hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2500.sound htau (by
                simp only [Batch0312.cell2500, Batch0312.tau2500, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33101 | hy33101
        · have hs331011 : InSquare (11/32) (33/160) (1/160) tau := by
            convert childLR hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx331011 | hx331011
          · rcases le_total tau.im (33/160 : ℝ) with hy331011 | hy331011
            · have hs3310110 : InSquare (109/320) (13/64) (1/320) tau := by
                convert childLL hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0311.cell2494.sound htau (by
                simp only [Batch0311.cell2494, Batch0311.tau2494, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310110 (by positivity) using 1 <;> norm_num)
            · have hs3310112 : InSquare (109/320) (67/320) (1/320) tau := by
                convert childUL hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0312.cell2496.sound htau (by
                simp only [Batch0312.cell2496, Batch0312.tau2496, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (33/160 : ℝ) with hy331011 | hy331011
            · have hs3310111 : InSquare (111/320) (13/64) (1/320) tau := by
                convert childLR hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0311.cell2495.sound htau (by
                simp only [Batch0311.cell2495, Batch0311.tau2495, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310111 (by positivity) using 1 <;> norm_num)
            · have hs3310113 : InSquare (111/320) (67/320) (1/320) tau := by
                convert childUR hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact (outside_3310113 htau hs3310113).elim
        · have hs331013 : InSquare (11/32) (7/32) (1/160) tau := by
            convert childUR hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx331013 | hx331013
          · rcases le_total tau.im (7/32 : ℝ) with hy331013 | hy331013
            · have hs3310130 : InSquare (109/320) (69/320) (1/320) tau := by
                convert childLL hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact Batch0312.cell2501.sound htau (by
                simp only [Batch0312.cell2501, Batch0312.tau2501, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310130 (by positivity) using 1 <;> norm_num)
            · have hs3310132 : InSquare (109/320) (71/320) (1/320) tau := by
                convert childUL hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310132 htau hs3310132).elim
          · rcases le_total tau.im (7/32 : ℝ) with hy331013 | hy331013
            · have hs3310131 : InSquare (111/320) (69/320) (1/320) tau := by
                convert childLR hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310131 htau hs3310131).elim
            · have hs3310133 : InSquare (111/320) (71/320) (1/320) tau := by
                convert childUR hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310133 htau hs3310133).elim
    · have hs33103 : InSquare (27/80) (19/80) (1/80) tau := by
        convert childUR hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx33103 | hx33103
      · rcases le_total tau.im (19/80 : ℝ) with hy33103 | hy33103
        · have hs331030 : InSquare (53/160) (37/160) (1/160) tau := by
            convert childLL hs33103 hx33103 hy33103 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx331030 | hx331030
          · rcases le_total tau.im (37/160 : ℝ) with hy331030 | hy331030
            · have hs3310300 : InSquare (21/64) (73/320) (1/320) tau := by
                convert childLL hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact Batch0314.cell2513.sound htau (by
                simp only [Batch0314.cell2513, Batch0314.tau2513, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310300 (by positivity) using 1 <;> norm_num)
            · have hs3310302 : InSquare (21/64) (15/64) (1/320) tau := by
                convert childUL hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact Batch0314.cell2514.sound htau (by
                simp only [Batch0314.cell2514, Batch0314.tau2514, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy331030 | hy331030
            · have hs3310301 : InSquare (107/320) (73/320) (1/320) tau := by
                convert childLR hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact (outside_3310301 htau hs3310301).elim
            · have hs3310303 : InSquare (107/320) (15/64) (1/320) tau := by
                convert childUR hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact (outside_3310303 htau hs3310303).elim
        · have hs331032 : InSquare (53/160) (39/160) (1/160) tau := by
            convert childUL hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331032 htau hs331032).elim
      · rcases le_total tau.im (19/80 : ℝ) with hy33103 | hy33103
        · have hs331031 : InSquare (11/32) (37/160) (1/160) tau := by
            convert childLR hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331031 htau hs331031).elim
        · have hs331033 : InSquare (11/32) (39/160) (1/160) tau := by
            convert childUR hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331033 htau hs331033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_33121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/16) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3312 | hx3312
  · rcases le_total tau.im (11/40 : ℝ) with hy3312 | hy3312
    · have hs33120 : InSquare (5/16) (21/80) (1/80) tau := by
        convert childLL hs hx3312 hy3312 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33120 | hx33120
      · rcases le_total tau.im (21/80 : ℝ) with hy33120 | hy33120
        · have hs331200 : InSquare (49/160) (41/160) (1/160) tau := by
            convert childLL hs33120 hx33120 hy33120 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331200 | hx331200
          · rcases le_total tau.im (41/160 : ℝ) with hy331200 | hy331200
            · have hs3312000 : InSquare (97/320) (81/320) (1/320) tau := by
                convert childLL hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2515.sound htau (by
                simp only [Batch0314.cell2515, Batch0314.tau2515, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312000 (by positivity) using 1 <;> norm_num)
            · have hs3312002 : InSquare (97/320) (83/320) (1/320) tau := by
                convert childUL hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2517.sound htau (by
                simp only [Batch0314.cell2517, Batch0314.tau2517, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy331200 | hy331200
            · have hs3312001 : InSquare (99/320) (81/320) (1/320) tau := by
                convert childLR hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2516.sound htau (by
                simp only [Batch0314.cell2516, Batch0314.tau2516, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312001 (by positivity) using 1 <;> norm_num)
            · have hs3312003 : InSquare (99/320) (83/320) (1/320) tau := by
                convert childUR hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2518.sound htau (by
                simp only [Batch0314.cell2518, Batch0314.tau2518, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312003 (by positivity) using 1 <;> norm_num)
        · have hs331202 : InSquare (49/160) (43/160) (1/160) tau := by
            convert childUL hs33120 hx33120 hy33120 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331202 | hx331202
          · rcases le_total tau.im (43/160 : ℝ) with hy331202 | hy331202
            · have hs3312020 : InSquare (97/320) (17/64) (1/320) tau := by
                convert childLL hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact Batch0314.cell2519.sound htau (by
                simp only [Batch0314.cell2519, Batch0314.tau2519, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312020 (by positivity) using 1 <;> norm_num)
            · have hs3312022 : InSquare (97/320) (87/320) (1/320) tau := by
                convert childUL hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312022 htau hs3312022).elim
          · rcases le_total tau.im (43/160 : ℝ) with hy331202 | hy331202
            · have hs3312021 : InSquare (99/320) (17/64) (1/320) tau := by
                convert childLR hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312021 htau hs3312021).elim
            · have hs3312023 : InSquare (99/320) (87/320) (1/320) tau := by
                convert childUR hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312023 htau hs3312023).elim
      · rcases le_total tau.im (21/80 : ℝ) with hy33120 | hy33120
        · have hs331201 : InSquare (51/160) (41/160) (1/160) tau := by
            convert childLR hs33120 hx33120 hy33120 using 1 <;> norm_num
          exact (outside_331201 htau hs331201).elim
        · have hs331203 : InSquare (51/160) (43/160) (1/160) tau := by
            convert childUR hs33120 hx33120 hy33120 using 1 <;> norm_num
          exact (outside_331203 htau hs331203).elim
    · have hs33122 : InSquare (5/16) (23/80) (1/80) tau := by
        convert childUL hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33122 htau hs33122).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy3312 | hy3312
    · have hs33121 : InSquare (27/80) (21/80) (1/80) tau := by
        convert childLR hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33121 htau hs33121).elim
    · have hs33123 : InSquare (27/80) (23/80) (1/80) tau := by
        convert childUR hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33123 htau hs33123).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312

end


