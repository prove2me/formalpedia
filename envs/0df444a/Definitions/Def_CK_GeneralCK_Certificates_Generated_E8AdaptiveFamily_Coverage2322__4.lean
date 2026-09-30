-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2322__4
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2322__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:24:06.967239+00:00
-- url     : https://prove2.me/theorems/55190d03-d973-400f-a8e2-f98b13b467f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2322 (+3 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2323, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2330, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2331).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0264
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0403
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0405
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0406
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0407
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0408
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0265
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0410
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0412
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0414
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0415
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0267
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0268
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0122
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_23222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/16) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/80) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322003 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/64) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-123/640) (227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-117/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/128) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/128) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2322 | hx2322
  · rcases le_total tau.im (3/8 : ℝ) with hy2322 | hy2322
    · have hs23220 : InSquare (-3/16) (29/80) (1/80) tau := by
        convert childLL hs hx2322 hy2322 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23220 | hx23220
      · rcases le_total tau.im (29/80 : ℝ) with hy23220 | hy23220
        · have hs232200 : InSquare (-31/160) (57/160) (1/160) tau := by
            convert childLL hs23220 hx23220 hy23220 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232200 | hx232200
          · rcases le_total tau.im (57/160 : ℝ) with hy232200 | hy232200
            · have hs2322000 : InSquare (-63/320) (113/320) (1/320) tau := by
                convert childLL hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322000 htau hs2322000).elim
            · have hs2322002 : InSquare (-63/320) (23/64) (1/320) tau := by
                convert childUL hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322002 htau hs2322002).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy232200 | hy232200
            · have hs2322001 : InSquare (-61/320) (113/320) (1/320) tau := by
                convert childLR hs232200 hx232200 hy232200 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx2322001 | hx2322001
              · rcases le_total tau.im (113/320 : ℝ) with hy2322001 | hy2322001
                · have hs23220010 : InSquare (-123/640) (45/128) (1/640) tau := by
                    convert childLL hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3227.sound htau (by
                    simp only [Batch0403.cell3227, Batch0403.tau3227, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220010 (by positivity) using 1 <;> norm_num)
                · have hs23220012 : InSquare (-123/640) (227/640) (1/640) tau := by
                    convert childUL hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact (outside_23220012 htau hs23220012).elim
              · rcases le_total tau.im (113/320 : ℝ) with hy2322001 | hy2322001
                · have hs23220011 : InSquare (-121/640) (45/128) (1/640) tau := by
                    convert childLR hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3228.sound htau (by
                    simp only [Batch0403.cell3228, Batch0403.tau3228, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220011 (by positivity) using 1 <;> norm_num)
                · have hs23220013 : InSquare (-121/640) (227/640) (1/640) tau := by
                    convert childUR hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3229.sound htau (by
                    simp only [Batch0403.cell3229, Batch0403.tau3229, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220013 (by positivity) using 1 <;> norm_num)
            · have hs2322003 : InSquare (-61/320) (23/64) (1/320) tau := by
                convert childUR hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322003 htau hs2322003).elim
        · have hs232202 : InSquare (-31/160) (59/160) (1/160) tau := by
            convert childUL hs23220 hx23220 hy23220 using 1 <;> norm_num
          exact (outside_232202 htau hs232202).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy23220 | hy23220
        · have hs232201 : InSquare (-29/160) (57/160) (1/160) tau := by
            convert childLR hs23220 hx23220 hy23220 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232201 | hx232201
          · rcases le_total tau.im (57/160 : ℝ) with hy232201 | hy232201
            · have hs2322010 : InSquare (-59/320) (113/320) (1/320) tau := by
                convert childLL hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx2322010 | hx2322010
              · rcases le_total tau.im (113/320 : ℝ) with hy2322010 | hy2322010
                · have hs23220100 : InSquare (-119/640) (45/128) (1/640) tau := by
                    convert childLL hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0403.cell3230.sound htau (by
                    simp only [Batch0403.cell3230, Batch0403.tau3230, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220100 (by positivity) using 1 <;> norm_num)
                · have hs23220102 : InSquare (-119/640) (227/640) (1/640) tau := by
                    convert childUL hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0404.cell3232.sound htau (by
                    simp only [Batch0404.cell3232, Batch0404.tau3232, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322010 | hy2322010
                · have hs23220101 : InSquare (-117/640) (45/128) (1/640) tau := by
                    convert childLR hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0403.cell3231.sound htau (by
                    simp only [Batch0403.cell3231, Batch0403.tau3231, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220101 (by positivity) using 1 <;> norm_num)
                · have hs23220103 : InSquare (-117/640) (227/640) (1/640) tau := by
                    convert childUR hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0404.cell3233.sound htau (by
                    simp only [Batch0404.cell3233, Batch0404.tau3233, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220103 (by positivity) using 1 <;> norm_num)
            · have hs2322012 : InSquare (-59/320) (23/64) (1/320) tau := by
                convert childUL hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx2322012 | hx2322012
              · rcases le_total tau.im (23/64 : ℝ) with hy2322012 | hy2322012
                · have hs23220120 : InSquare (-119/640) (229/640) (1/640) tau := by
                    convert childLL hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220120 htau hs23220120).elim
                · have hs23220122 : InSquare (-119/640) (231/640) (1/640) tau := by
                    convert childUL hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220122 htau hs23220122).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy2322012 | hy2322012
                · have hs23220121 : InSquare (-117/640) (229/640) (1/640) tau := by
                    convert childLR hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact Batch0404.cell3238.sound htau (by
                    simp only [Batch0404.cell3238, Batch0404.tau3238, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220121 (by positivity) using 1 <;> norm_num)
                · have hs23220123 : InSquare (-117/640) (231/640) (1/640) tau := by
                    convert childUR hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220123 htau hs23220123).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy232201 | hy232201
            · have hs2322011 : InSquare (-57/320) (113/320) (1/320) tau := by
                convert childLR hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx2322011 | hx2322011
              · rcases le_total tau.im (113/320 : ℝ) with hy2322011 | hy2322011
                · have hs23220110 : InSquare (-23/128) (45/128) (1/640) tau := by
                    convert childLL hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3234.sound htau (by
                    simp only [Batch0404.cell3234, Batch0404.tau3234, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220110 (by positivity) using 1 <;> norm_num)
                · have hs23220112 : InSquare (-23/128) (227/640) (1/640) tau := by
                    convert childUL hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3236.sound htau (by
                    simp only [Batch0404.cell3236, Batch0404.tau3236, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322011 | hy2322011
                · have hs23220111 : InSquare (-113/640) (45/128) (1/640) tau := by
                    convert childLR hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3235.sound htau (by
                    simp only [Batch0404.cell3235, Batch0404.tau3235, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220111 (by positivity) using 1 <;> norm_num)
                · have hs23220113 : InSquare (-113/640) (227/640) (1/640) tau := by
                    convert childUR hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3237.sound htau (by
                    simp only [Batch0404.cell3237, Batch0404.tau3237, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220113 (by positivity) using 1 <;> norm_num)
            · have hs2322013 : InSquare (-57/320) (23/64) (1/320) tau := by
                convert childUR hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx2322013 | hx2322013
              · rcases le_total tau.im (23/64 : ℝ) with hy2322013 | hy2322013
                · have hs23220130 : InSquare (-23/128) (229/640) (1/640) tau := by
                    convert childLL hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0404.cell3239.sound htau (by
                    simp only [Batch0404.cell3239, Batch0404.tau3239, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220130 (by positivity) using 1 <;> norm_num)
                · have hs23220132 : InSquare (-23/128) (231/640) (1/640) tau := by
                    convert childUL hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact (outside_23220132 htau hs23220132).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy2322013 | hy2322013
                · have hs23220131 : InSquare (-113/640) (229/640) (1/640) tau := by
                    convert childLR hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0405.cell3240.sound htau (by
                    simp only [Batch0405.cell3240, Batch0405.tau3240, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220131 (by positivity) using 1 <;> norm_num)
                · have hs23220133 : InSquare (-113/640) (231/640) (1/640) tau := by
                    convert childUR hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0405.cell3241.sound htau (by
                    simp only [Batch0405.cell3241, Batch0405.tau3241, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220133 (by positivity) using 1 <;> norm_num)
        · have hs232203 : InSquare (-29/160) (59/160) (1/160) tau := by
            convert childUR hs23220 hx23220 hy23220 using 1 <;> norm_num
          exact (outside_232203 htau hs232203).elim
    · have hs23222 : InSquare (-3/16) (31/80) (1/80) tau := by
        convert childUL hs hx2322 hy2322 using 1 <;> norm_num
      exact (outside_23222 htau hs23222).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2322 | hy2322
    · have hs23221 : InSquare (-13/80) (29/80) (1/80) tau := by
        convert childLR hs hx2322 hy2322 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23221 | hx23221
      · rcases le_total tau.im (29/80 : ℝ) with hy23221 | hy23221
        · have hs232210 : InSquare (-27/160) (57/160) (1/160) tau := by
            convert childLL hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232210 | hx232210
          · rcases le_total tau.im (57/160 : ℝ) with hy232210 | hy232210
            · have hs2322100 : InSquare (-11/64) (113/320) (1/320) tau := by
                convert childLL hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322100 | hx2322100
              · rcases le_total tau.im (113/320 : ℝ) with hy2322100 | hy2322100
                · have hs23221000 : InSquare (-111/640) (45/128) (1/640) tau := by
                    convert childLL hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3242.sound htau (by
                    simp only [Batch0405.cell3242, Batch0405.tau3242, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221000 (by positivity) using 1 <;> norm_num)
                · have hs23221002 : InSquare (-111/640) (227/640) (1/640) tau := by
                    convert childUL hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3244.sound htau (by
                    simp only [Batch0405.cell3244, Batch0405.tau3244, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322100 | hy2322100
                · have hs23221001 : InSquare (-109/640) (45/128) (1/640) tau := by
                    convert childLR hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3243.sound htau (by
                    simp only [Batch0405.cell3243, Batch0405.tau3243, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221001 (by positivity) using 1 <;> norm_num)
                · have hs23221003 : InSquare (-109/640) (227/640) (1/640) tau := by
                    convert childUR hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3245.sound htau (by
                    simp only [Batch0405.cell3245, Batch0405.tau3245, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221003 (by positivity) using 1 <;> norm_num)
            · have hs2322102 : InSquare (-11/64) (23/64) (1/320) tau := by
                convert childUL hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322102 | hx2322102
              · rcases le_total tau.im (23/64 : ℝ) with hy2322102 | hy2322102
                · have hs23221020 : InSquare (-111/640) (229/640) (1/640) tau := by
                    convert childLL hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0405.cell3246.sound htau (by
                    simp only [Batch0405.cell3246, Batch0405.tau3246, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221020 (by positivity) using 1 <;> norm_num)
                · have hs23221022 : InSquare (-111/640) (231/640) (1/640) tau := by
                    convert childUL hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0406.cell3248.sound htau (by
                    simp only [Batch0406.cell3248, Batch0406.tau3248, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322102 | hy2322102
                · have hs23221021 : InSquare (-109/640) (229/640) (1/640) tau := by
                    convert childLR hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0405.cell3247.sound htau (by
                    simp only [Batch0405.cell3247, Batch0405.tau3247, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221021 (by positivity) using 1 <;> norm_num)
                · have hs23221023 : InSquare (-109/640) (231/640) (1/640) tau := by
                    convert childUR hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0406.cell3249.sound htau (by
                    simp only [Batch0406.cell3249, Batch0406.tau3249, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232210 | hy232210
            · have hs2322101 : InSquare (-53/320) (113/320) (1/320) tau := by
                convert childLR hs232210 hx232210 hy232210 using 1 <;> norm_num
              exact Batch0264.cell2113.sound htau (by
                simp only [Batch0264.cell2113, Batch0264.tau2113, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322101 (by positivity) using 1 <;> norm_num)
            · have hs2322103 : InSquare (-53/320) (23/64) (1/320) tau := by
                convert childUR hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx2322103 | hx2322103
              · rcases le_total tau.im (23/64 : ℝ) with hy2322103 | hy2322103
                · have hs23221030 : InSquare (-107/640) (229/640) (1/640) tau := by
                    convert childLL hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3250.sound htau (by
                    simp only [Batch0406.cell3250, Batch0406.tau3250, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221030 (by positivity) using 1 <;> norm_num)
                · have hs23221032 : InSquare (-107/640) (231/640) (1/640) tau := by
                    convert childUL hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3252.sound htau (by
                    simp only [Batch0406.cell3252, Batch0406.tau3252, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322103 | hy2322103
                · have hs23221031 : InSquare (-21/128) (229/640) (1/640) tau := by
                    convert childLR hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3251.sound htau (by
                    simp only [Batch0406.cell3251, Batch0406.tau3251, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221031 (by positivity) using 1 <;> norm_num)
                · have hs23221033 : InSquare (-21/128) (231/640) (1/640) tau := by
                    convert childUR hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3253.sound htau (by
                    simp only [Batch0406.cell3253, Batch0406.tau3253, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221033 (by positivity) using 1 <;> norm_num)
        · have hs232212 : InSquare (-27/160) (59/160) (1/160) tau := by
            convert childUL hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232212 | hx232212
          · rcases le_total tau.im (59/160 : ℝ) with hy232212 | hy232212
            · have hs2322120 : InSquare (-11/64) (117/320) (1/320) tau := by
                convert childLL hs232212 hx232212 hy232212 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322120 | hx2322120
              · rcases le_total tau.im (117/320 : ℝ) with hy2322120 | hy2322120
                · have hs23221200 : InSquare (-111/640) (233/640) (1/640) tau := by
                    convert childLL hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221200 htau hs23221200).elim
                · have hs23221202 : InSquare (-111/640) (47/128) (1/640) tau := by
                    convert childUL hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221202 htau hs23221202).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy2322120 | hy2322120
                · have hs23221201 : InSquare (-109/640) (233/640) (1/640) tau := by
                    convert childLR hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact Batch0407.cell3262.sound htau (by
                    simp only [Batch0407.cell3262, Batch0407.tau3262, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221201 (by positivity) using 1 <;> norm_num)
                · have hs23221203 : InSquare (-109/640) (47/128) (1/640) tau := by
                    convert childUR hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221203 htau hs23221203).elim
            · have hs2322122 : InSquare (-11/64) (119/320) (1/320) tau := by
                convert childUL hs232212 hx232212 hy232212 using 1 <;> norm_num
              exact (outside_2322122 htau hs2322122).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy232212 | hy232212
            · have hs2322121 : InSquare (-53/320) (117/320) (1/320) tau := by
                convert childLR hs232212 hx232212 hy232212 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx2322121 | hx2322121
              · rcases le_total tau.im (117/320 : ℝ) with hy2322121 | hy2322121
                · have hs23221210 : InSquare (-107/640) (233/640) (1/640) tau := by
                    convert childLL hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact Batch0407.cell3263.sound htau (by
                    simp only [Batch0407.cell3263, Batch0407.tau3263, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221210 (by positivity) using 1 <;> norm_num)
                · have hs23221212 : InSquare (-107/640) (47/128) (1/640) tau := by
                    convert childUL hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact (outside_23221212 htau hs23221212).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy2322121 | hy2322121
                · have hs23221211 : InSquare (-21/128) (233/640) (1/640) tau := by
                    convert childLR hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact Batch0408.cell3264.sound htau (by
                    simp only [Batch0408.cell3264, Batch0408.tau3264, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221211 (by positivity) using 1 <;> norm_num)
                · have hs23221213 : InSquare (-21/128) (47/128) (1/640) tau := by
                    convert childUR hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact (outside_23221213 htau hs23221213).elim
            · have hs2322123 : InSquare (-53/320) (119/320) (1/320) tau := by
                convert childUR hs232212 hx232212 hy232212 using 1 <;> norm_num
              exact (outside_2322123 htau hs2322123).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy23221 | hy23221
        · have hs232211 : InSquare (-5/32) (57/160) (1/160) tau := by
            convert childLR hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232211 | hx232211
          · rcases le_total tau.im (57/160 : ℝ) with hy232211 | hy232211
            · have hs2322110 : InSquare (-51/320) (113/320) (1/320) tau := by
                convert childLL hs232211 hx232211 hy232211 using 1 <;> norm_num
              exact Batch0264.cell2114.sound htau (by
                simp only [Batch0264.cell2114, Batch0264.tau2114, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322110 (by positivity) using 1 <;> norm_num)
            · have hs2322112 : InSquare (-51/320) (23/64) (1/320) tau := by
                convert childUL hs232211 hx232211 hy232211 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx2322112 | hx2322112
              · rcases le_total tau.im (23/64 : ℝ) with hy2322112 | hy2322112
                · have hs23221120 : InSquare (-103/640) (229/640) (1/640) tau := by
                    convert childLL hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0406.cell3254.sound htau (by
                    simp only [Batch0406.cell3254, Batch0406.tau3254, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221120 (by positivity) using 1 <;> norm_num)
                · have hs23221122 : InSquare (-103/640) (231/640) (1/640) tau := by
                    convert childUL hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0407.cell3256.sound htau (by
                    simp only [Batch0407.cell3256, Batch0407.tau3256, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322112 | hy2322112
                · have hs23221121 : InSquare (-101/640) (229/640) (1/640) tau := by
                    convert childLR hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0406.cell3255.sound htau (by
                    simp only [Batch0406.cell3255, Batch0406.tau3255, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221121 (by positivity) using 1 <;> norm_num)
                · have hs23221123 : InSquare (-101/640) (231/640) (1/640) tau := by
                    convert childUR hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0407.cell3257.sound htau (by
                    simp only [Batch0407.cell3257, Batch0407.tau3257, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232211 | hy232211
            · have hs2322111 : InSquare (-49/320) (113/320) (1/320) tau := by
                convert childLR hs232211 hx232211 hy232211 using 1 <;> norm_num
              exact Batch0264.cell2115.sound htau (by
                simp only [Batch0264.cell2115, Batch0264.tau2115, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322111 (by positivity) using 1 <;> norm_num)
            · have hs2322113 : InSquare (-49/320) (23/64) (1/320) tau := by
                convert childUR hs232211 hx232211 hy232211 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322113 | hx2322113
              · rcases le_total tau.im (23/64 : ℝ) with hy2322113 | hy2322113
                · have hs23221130 : InSquare (-99/640) (229/640) (1/640) tau := by
                    convert childLL hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3258.sound htau (by
                    simp only [Batch0407.cell3258, Batch0407.tau3258, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221130 (by positivity) using 1 <;> norm_num)
                · have hs23221132 : InSquare (-99/640) (231/640) (1/640) tau := by
                    convert childUL hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3260.sound htau (by
                    simp only [Batch0407.cell3260, Batch0407.tau3260, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322113 | hy2322113
                · have hs23221131 : InSquare (-97/640) (229/640) (1/640) tau := by
                    convert childLR hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3259.sound htau (by
                    simp only [Batch0407.cell3259, Batch0407.tau3259, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221131 (by positivity) using 1 <;> norm_num)
                · have hs23221133 : InSquare (-97/640) (231/640) (1/640) tau := by
                    convert childUR hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3261.sound htau (by
                    simp only [Batch0407.cell3261, Batch0407.tau3261, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221133 (by positivity) using 1 <;> norm_num)
        · have hs232213 : InSquare (-5/32) (59/160) (1/160) tau := by
            convert childUR hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232213 | hx232213
          · rcases le_total tau.im (59/160 : ℝ) with hy232213 | hy232213
            · have hs2322130 : InSquare (-51/320) (117/320) (1/320) tau := by
                convert childLL hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx2322130 | hx2322130
              · rcases le_total tau.im (117/320 : ℝ) with hy2322130 | hy2322130
                · have hs23221300 : InSquare (-103/640) (233/640) (1/640) tau := by
                    convert childLL hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3265.sound htau (by
                    simp only [Batch0408.cell3265, Batch0408.tau3265, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221300 (by positivity) using 1 <;> norm_num)
                · have hs23221302 : InSquare (-103/640) (47/128) (1/640) tau := by
                    convert childUL hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3267.sound htau (by
                    simp only [Batch0408.cell3267, Batch0408.tau3267, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2322130 | hy2322130
                · have hs23221301 : InSquare (-101/640) (233/640) (1/640) tau := by
                    convert childLR hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3266.sound htau (by
                    simp only [Batch0408.cell3266, Batch0408.tau3266, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221301 (by positivity) using 1 <;> norm_num)
                · have hs23221303 : InSquare (-101/640) (47/128) (1/640) tau := by
                    convert childUR hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3268.sound htau (by
                    simp only [Batch0408.cell3268, Batch0408.tau3268, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221303 (by positivity) using 1 <;> norm_num)
            · have hs2322132 : InSquare (-51/320) (119/320) (1/320) tau := by
                convert childUL hs232213 hx232213 hy232213 using 1 <;> norm_num
              exact (outside_2322132 htau hs2322132).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy232213 | hy232213
            · have hs2322131 : InSquare (-49/320) (117/320) (1/320) tau := by
                convert childLR hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322131 | hx2322131
              · rcases le_total tau.im (117/320 : ℝ) with hy2322131 | hy2322131
                · have hs23221310 : InSquare (-99/640) (233/640) (1/640) tau := by
                    convert childLL hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3269.sound htau (by
                    simp only [Batch0408.cell3269, Batch0408.tau3269, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221310 (by positivity) using 1 <;> norm_num)
                · have hs23221312 : InSquare (-99/640) (47/128) (1/640) tau := by
                    convert childUL hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3271.sound htau (by
                    simp only [Batch0408.cell3271, Batch0408.tau3271, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2322131 | hy2322131
                · have hs23221311 : InSquare (-97/640) (233/640) (1/640) tau := by
                    convert childLR hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3270.sound htau (by
                    simp only [Batch0408.cell3270, Batch0408.tau3270, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221311 (by positivity) using 1 <;> norm_num)
                · have hs23221313 : InSquare (-97/640) (47/128) (1/640) tau := by
                    convert childUR hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0409.cell3272.sound htau (by
                    simp only [Batch0409.cell3272, Batch0409.tau3272, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221313 (by positivity) using 1 <;> norm_num)
            · have hs2322133 : InSquare (-49/320) (119/320) (1/320) tau := by
                convert childUR hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322133 | hx2322133
              · rcases le_total tau.im (119/320 : ℝ) with hy2322133 | hy2322133
                · have hs23221330 : InSquare (-99/640) (237/640) (1/640) tau := by
                    convert childLL hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact Batch0409.cell3273.sound htau (by
                    simp only [Batch0409.cell3273, Batch0409.tau3273, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221330 (by positivity) using 1 <;> norm_num)
                · have hs23221332 : InSquare (-99/640) (239/640) (1/640) tau := by
                    convert childUL hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact (outside_23221332 htau hs23221332).elim
              · rcases le_total tau.im (119/320 : ℝ) with hy2322133 | hy2322133
                · have hs23221331 : InSquare (-97/640) (237/640) (1/640) tau := by
                    convert childLR hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact Batch0409.cell3274.sound htau (by
                    simp only [Batch0409.cell3274, Batch0409.tau3274, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221331 (by positivity) using 1 <;> norm_num)
                · have hs23221333 : InSquare (-97/640) (239/640) (1/640) tau := by
                    convert childUR hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact (outside_23221333 htau hs23221333).elim
    · have hs23223 : InSquare (-13/80) (31/80) (1/80) tau := by
        convert childUR hs hx2322 hy2322 using 1 <;> norm_num
      exact (outside_23223 htau hs23223).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_232322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/64) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/128) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-77/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/128) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2323 | hx2323
  · rcases le_total tau.im (3/8 : ℝ) with hy2323 | hy2323
    · have hs23230 : InSquare (-11/80) (29/80) (1/80) tau := by
        convert childLL hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23230 | hx23230
      · rcases le_total tau.im (29/80 : ℝ) with hy23230 | hy23230
        · have hs232300 : InSquare (-23/160) (57/160) (1/160) tau := by
            convert childLL hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232300 | hx232300
          · rcases le_total tau.im (57/160 : ℝ) with hy232300 | hy232300
            · have hs2323000 : InSquare (-47/320) (113/320) (1/320) tau := by
                convert childLL hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2116.sound htau (by
                simp only [Batch0264.cell2116, Batch0264.tau2116, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323000 (by positivity) using 1 <;> norm_num)
            · have hs2323002 : InSquare (-47/320) (23/64) (1/320) tau := by
                convert childUL hs232300 hx232300 hy232300 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323002 | hx2323002
              · rcases le_total tau.im (23/64 : ℝ) with hy2323002 | hy2323002
                · have hs23230020 : InSquare (-19/128) (229/640) (1/640) tau := by
                    convert childLL hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3275.sound htau (by
                    simp only [Batch0409.cell3275, Batch0409.tau3275, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230020 (by positivity) using 1 <;> norm_num)
                · have hs23230022 : InSquare (-19/128) (231/640) (1/640) tau := by
                    convert childUL hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3277.sound htau (by
                    simp only [Batch0409.cell3277, Batch0409.tau3277, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2323002 | hy2323002
                · have hs23230021 : InSquare (-93/640) (229/640) (1/640) tau := by
                    convert childLR hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3276.sound htau (by
                    simp only [Batch0409.cell3276, Batch0409.tau3276, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230021 (by positivity) using 1 <;> norm_num)
                · have hs23230023 : InSquare (-93/640) (231/640) (1/640) tau := by
                    convert childUR hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3278.sound htau (by
                    simp only [Batch0409.cell3278, Batch0409.tau3278, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232300 | hy232300
            · have hs2323001 : InSquare (-9/64) (113/320) (1/320) tau := by
                convert childLR hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2117.sound htau (by
                simp only [Batch0264.cell2117, Batch0264.tau2117, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323001 (by positivity) using 1 <;> norm_num)
            · have hs2323003 : InSquare (-9/64) (23/64) (1/320) tau := by
                convert childUR hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2118.sound htau (by
                simp only [Batch0264.cell2118, Batch0264.tau2118, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323003 (by positivity) using 1 <;> norm_num)
        · have hs232302 : InSquare (-23/160) (59/160) (1/160) tau := by
            convert childUL hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232302 | hx232302
          · rcases le_total tau.im (59/160 : ℝ) with hy232302 | hy232302
            · have hs2323020 : InSquare (-47/320) (117/320) (1/320) tau := by
                convert childLL hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323020 | hx2323020
              · rcases le_total tau.im (117/320 : ℝ) with hy2323020 | hy2323020
                · have hs23230200 : InSquare (-19/128) (233/640) (1/640) tau := by
                    convert childLL hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0409.cell3279.sound htau (by
                    simp only [Batch0409.cell3279, Batch0409.tau3279, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230200 (by positivity) using 1 <;> norm_num)
                · have hs23230202 : InSquare (-19/128) (47/128) (1/640) tau := by
                    convert childUL hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3281.sound htau (by
                    simp only [Batch0410.cell3281, Batch0410.tau3281, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323020 | hy2323020
                · have hs23230201 : InSquare (-93/640) (233/640) (1/640) tau := by
                    convert childLR hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3280.sound htau (by
                    simp only [Batch0410.cell3280, Batch0410.tau3280, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230201 (by positivity) using 1 <;> norm_num)
                · have hs23230203 : InSquare (-93/640) (47/128) (1/640) tau := by
                    convert childUR hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3282.sound htau (by
                    simp only [Batch0410.cell3282, Batch0410.tau3282, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230203 (by positivity) using 1 <;> norm_num)
            · have hs2323022 : InSquare (-47/320) (119/320) (1/320) tau := by
                convert childUL hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323022 | hx2323022
              · rcases le_total tau.im (119/320 : ℝ) with hy2323022 | hy2323022
                · have hs23230220 : InSquare (-19/128) (237/640) (1/640) tau := by
                    convert childLL hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0410.cell3287.sound htau (by
                    simp only [Batch0410.cell3287, Batch0410.tau3287, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230220 (by positivity) using 1 <;> norm_num)
                · have hs23230222 : InSquare (-19/128) (239/640) (1/640) tau := by
                    convert childUL hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3289.sound htau (by
                    simp only [Batch0411.cell3289, Batch0411.tau3289, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323022 | hy2323022
                · have hs23230221 : InSquare (-93/640) (237/640) (1/640) tau := by
                    convert childLR hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3288.sound htau (by
                    simp only [Batch0411.cell3288, Batch0411.tau3288, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230221 (by positivity) using 1 <;> norm_num)
                · have hs23230223 : InSquare (-93/640) (239/640) (1/640) tau := by
                    convert childUR hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3290.sound htau (by
                    simp only [Batch0411.cell3290, Batch0411.tau3290, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232302 | hy232302
            · have hs2323021 : InSquare (-9/64) (117/320) (1/320) tau := by
                convert childLR hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323021 | hx2323021
              · rcases le_total tau.im (117/320 : ℝ) with hy2323021 | hy2323021
                · have hs23230210 : InSquare (-91/640) (233/640) (1/640) tau := by
                    convert childLL hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3283.sound htau (by
                    simp only [Batch0410.cell3283, Batch0410.tau3283, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230210 (by positivity) using 1 <;> norm_num)
                · have hs23230212 : InSquare (-91/640) (47/128) (1/640) tau := by
                    convert childUL hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3285.sound htau (by
                    simp only [Batch0410.cell3285, Batch0410.tau3285, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323021 | hy2323021
                · have hs23230211 : InSquare (-89/640) (233/640) (1/640) tau := by
                    convert childLR hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3284.sound htau (by
                    simp only [Batch0410.cell3284, Batch0410.tau3284, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230211 (by positivity) using 1 <;> norm_num)
                · have hs23230213 : InSquare (-89/640) (47/128) (1/640) tau := by
                    convert childUR hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3286.sound htau (by
                    simp only [Batch0410.cell3286, Batch0410.tau3286, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230213 (by positivity) using 1 <;> norm_num)
            · have hs2323023 : InSquare (-9/64) (119/320) (1/320) tau := by
                convert childUR hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323023 | hx2323023
              · rcases le_total tau.im (119/320 : ℝ) with hy2323023 | hy2323023
                · have hs23230230 : InSquare (-91/640) (237/640) (1/640) tau := by
                    convert childLL hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3291.sound htau (by
                    simp only [Batch0411.cell3291, Batch0411.tau3291, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230230 (by positivity) using 1 <;> norm_num)
                · have hs23230232 : InSquare (-91/640) (239/640) (1/640) tau := by
                    convert childUL hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3293.sound htau (by
                    simp only [Batch0411.cell3293, Batch0411.tau3293, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323023 | hy2323023
                · have hs23230231 : InSquare (-89/640) (237/640) (1/640) tau := by
                    convert childLR hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3292.sound htau (by
                    simp only [Batch0411.cell3292, Batch0411.tau3292, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230231 (by positivity) using 1 <;> norm_num)
                · have hs23230233 : InSquare (-89/640) (239/640) (1/640) tau := by
                    convert childUR hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3294.sound htau (by
                    simp only [Batch0411.cell3294, Batch0411.tau3294, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23230 | hy23230
        · have hs232301 : InSquare (-21/160) (57/160) (1/160) tau := by
            convert childLR hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232301 | hx232301
          · rcases le_total tau.im (57/160 : ℝ) with hy232301 | hy232301
            · have hs2323010 : InSquare (-43/320) (113/320) (1/320) tau := by
                convert childLL hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0264.cell2119.sound htau (by
                simp only [Batch0264.cell2119, Batch0264.tau2119, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323010 (by positivity) using 1 <;> norm_num)
            · have hs2323012 : InSquare (-43/320) (23/64) (1/320) tau := by
                convert childUL hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2121.sound htau (by
                simp only [Batch0265.cell2121, Batch0265.tau2121, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232301 | hy232301
            · have hs2323011 : InSquare (-41/320) (113/320) (1/320) tau := by
                convert childLR hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2120.sound htau (by
                simp only [Batch0265.cell2120, Batch0265.tau2120, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323011 (by positivity) using 1 <;> norm_num)
            · have hs2323013 : InSquare (-41/320) (23/64) (1/320) tau := by
                convert childUR hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2122.sound htau (by
                simp only [Batch0265.cell2122, Batch0265.tau2122, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323013 (by positivity) using 1 <;> norm_num)
        · have hs232303 : InSquare (-21/160) (59/160) (1/160) tau := by
            convert childUR hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232303 | hx232303
          · rcases le_total tau.im (59/160 : ℝ) with hy232303 | hy232303
            · have hs2323030 : InSquare (-43/320) (117/320) (1/320) tau := by
                convert childLL hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323030 | hx2323030
              · rcases le_total tau.im (117/320 : ℝ) with hy2323030 | hy2323030
                · have hs23230300 : InSquare (-87/640) (233/640) (1/640) tau := by
                    convert childLL hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0411.cell3295.sound htau (by
                    simp only [Batch0411.cell3295, Batch0411.tau3295, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230300 (by positivity) using 1 <;> norm_num)
                · have hs23230302 : InSquare (-87/640) (47/128) (1/640) tau := by
                    convert childUL hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3297.sound htau (by
                    simp only [Batch0412.cell3297, Batch0412.tau3297, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323030 | hy2323030
                · have hs23230301 : InSquare (-17/128) (233/640) (1/640) tau := by
                    convert childLR hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3296.sound htau (by
                    simp only [Batch0412.cell3296, Batch0412.tau3296, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230301 (by positivity) using 1 <;> norm_num)
                · have hs23230303 : InSquare (-17/128) (47/128) (1/640) tau := by
                    convert childUR hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3298.sound htau (by
                    simp only [Batch0412.cell3298, Batch0412.tau3298, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230303 (by positivity) using 1 <;> norm_num)
            · have hs2323032 : InSquare (-43/320) (119/320) (1/320) tau := by
                convert childUL hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323032 | hx2323032
              · rcases le_total tau.im (119/320 : ℝ) with hy2323032 | hy2323032
                · have hs23230320 : InSquare (-87/640) (237/640) (1/640) tau := by
                    convert childLL hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0412.cell3303.sound htau (by
                    simp only [Batch0412.cell3303, Batch0412.tau3303, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230320 (by positivity) using 1 <;> norm_num)
                · have hs23230322 : InSquare (-87/640) (239/640) (1/640) tau := by
                    convert childUL hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3305.sound htau (by
                    simp only [Batch0413.cell3305, Batch0413.tau3305, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323032 | hy2323032
                · have hs23230321 : InSquare (-17/128) (237/640) (1/640) tau := by
                    convert childLR hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3304.sound htau (by
                    simp only [Batch0413.cell3304, Batch0413.tau3304, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230321 (by positivity) using 1 <;> norm_num)
                · have hs23230323 : InSquare (-17/128) (239/640) (1/640) tau := by
                    convert childUR hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3306.sound htau (by
                    simp only [Batch0413.cell3306, Batch0413.tau3306, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232303 | hy232303
            · have hs2323031 : InSquare (-41/320) (117/320) (1/320) tau := by
                convert childLR hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323031 | hx2323031
              · rcases le_total tau.im (117/320 : ℝ) with hy2323031 | hy2323031
                · have hs23230310 : InSquare (-83/640) (233/640) (1/640) tau := by
                    convert childLL hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3299.sound htau (by
                    simp only [Batch0412.cell3299, Batch0412.tau3299, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230310 (by positivity) using 1 <;> norm_num)
                · have hs23230312 : InSquare (-83/640) (47/128) (1/640) tau := by
                    convert childUL hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3301.sound htau (by
                    simp only [Batch0412.cell3301, Batch0412.tau3301, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323031 | hy2323031
                · have hs23230311 : InSquare (-81/640) (233/640) (1/640) tau := by
                    convert childLR hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3300.sound htau (by
                    simp only [Batch0412.cell3300, Batch0412.tau3300, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230311 (by positivity) using 1 <;> norm_num)
                · have hs23230313 : InSquare (-81/640) (47/128) (1/640) tau := by
                    convert childUR hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3302.sound htau (by
                    simp only [Batch0412.cell3302, Batch0412.tau3302, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230313 (by positivity) using 1 <;> norm_num)
            · have hs2323033 : InSquare (-41/320) (119/320) (1/320) tau := by
                convert childUR hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323033 | hx2323033
              · rcases le_total tau.im (119/320 : ℝ) with hy2323033 | hy2323033
                · have hs23230330 : InSquare (-83/640) (237/640) (1/640) tau := by
                    convert childLL hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3307.sound htau (by
                    simp only [Batch0413.cell3307, Batch0413.tau3307, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230330 (by positivity) using 1 <;> norm_num)
                · have hs23230332 : InSquare (-83/640) (239/640) (1/640) tau := by
                    convert childUL hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3309.sound htau (by
                    simp only [Batch0413.cell3309, Batch0413.tau3309, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323033 | hy2323033
                · have hs23230331 : InSquare (-81/640) (237/640) (1/640) tau := by
                    convert childLR hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3308.sound htau (by
                    simp only [Batch0413.cell3308, Batch0413.tau3308, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230331 (by positivity) using 1 <;> norm_num)
                · have hs23230333 : InSquare (-81/640) (239/640) (1/640) tau := by
                    convert childUR hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3310.sound htau (by
                    simp only [Batch0413.cell3310, Batch0413.tau3310, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230333 (by positivity) using 1 <;> norm_num)
    · have hs23232 : InSquare (-11/80) (31/80) (1/80) tau := by
        convert childUL hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23232 | hx23232
      · rcases le_total tau.im (31/80 : ℝ) with hy23232 | hy23232
        · have hs232320 : InSquare (-23/160) (61/160) (1/160) tau := by
            convert childLL hs23232 hx23232 hy23232 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232320 | hx232320
          · rcases le_total tau.im (61/160 : ℝ) with hy232320 | hy232320
            · have hs2323200 : InSquare (-47/320) (121/320) (1/320) tau := by
                convert childLL hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323200 htau hs2323200).elim
            · have hs2323202 : InSquare (-47/320) (123/320) (1/320) tau := by
                convert childUL hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323202 htau hs2323202).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232320 | hy232320
            · have hs2323201 : InSquare (-9/64) (121/320) (1/320) tau := by
                convert childLR hs232320 hx232320 hy232320 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323201 | hx2323201
              · rcases le_total tau.im (121/320 : ℝ) with hy2323201 | hy2323201
                · have hs23232010 : InSquare (-91/640) (241/640) (1/640) tau := by
                    convert childLL hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232010 htau hs23232010).elim
                · have hs23232012 : InSquare (-91/640) (243/640) (1/640) tau := by
                    convert childUL hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232012 htau hs23232012).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy2323201 | hy2323201
                · have hs23232011 : InSquare (-89/640) (241/640) (1/640) tau := by
                    convert childLR hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact Batch0415.cell3327.sound htau (by
                    simp only [Batch0415.cell3327, Batch0415.tau3327, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232011 (by positivity) using 1 <;> norm_num)
                · have hs23232013 : InSquare (-89/640) (243/640) (1/640) tau := by
                    convert childUR hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232013 htau hs23232013).elim
            · have hs2323203 : InSquare (-9/64) (123/320) (1/320) tau := by
                convert childUR hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323203 htau hs2323203).elim
        · have hs232322 : InSquare (-23/160) (63/160) (1/160) tau := by
            convert childUL hs23232 hx23232 hy23232 using 1 <;> norm_num
          exact (outside_232322 htau hs232322).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23232 | hy23232
        · have hs232321 : InSquare (-21/160) (61/160) (1/160) tau := by
            convert childLR hs23232 hx23232 hy23232 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232321 | hx232321
          · rcases le_total tau.im (61/160 : ℝ) with hy232321 | hy232321
            · have hs2323210 : InSquare (-43/320) (121/320) (1/320) tau := by
                convert childLL hs232321 hx232321 hy232321 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323210 | hx2323210
              · rcases le_total tau.im (121/320 : ℝ) with hy2323210 | hy2323210
                · have hs23232100 : InSquare (-87/640) (241/640) (1/640) tau := by
                    convert childLL hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact Batch0416.cell3328.sound htau (by
                    simp only [Batch0416.cell3328, Batch0416.tau3328, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232100 (by positivity) using 1 <;> norm_num)
                · have hs23232102 : InSquare (-87/640) (243/640) (1/640) tau := by
                    convert childUL hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact (outside_23232102 htau hs23232102).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy2323210 | hy2323210
                · have hs23232101 : InSquare (-17/128) (241/640) (1/640) tau := by
                    convert childLR hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact Batch0416.cell3329.sound htau (by
                    simp only [Batch0416.cell3329, Batch0416.tau3329, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232101 (by positivity) using 1 <;> norm_num)
                · have hs23232103 : InSquare (-17/128) (243/640) (1/640) tau := by
                    convert childUR hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact (outside_23232103 htau hs23232103).elim
            · have hs2323212 : InSquare (-43/320) (123/320) (1/320) tau := by
                convert childUL hs232321 hx232321 hy232321 using 1 <;> norm_num
              exact (outside_2323212 htau hs2323212).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232321 | hy232321
            · have hs2323211 : InSquare (-41/320) (121/320) (1/320) tau := by
                convert childLR hs232321 hx232321 hy232321 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323211 | hx2323211
              · rcases le_total tau.im (121/320 : ℝ) with hy2323211 | hy2323211
                · have hs23232110 : InSquare (-83/640) (241/640) (1/640) tau := by
                    convert childLL hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3330.sound htau (by
                    simp only [Batch0416.cell3330, Batch0416.tau3330, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232110 (by positivity) using 1 <;> norm_num)
                · have hs23232112 : InSquare (-83/640) (243/640) (1/640) tau := by
                    convert childUL hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3332.sound htau (by
                    simp only [Batch0416.cell3332, Batch0416.tau3332, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323211 | hy2323211
                · have hs23232111 : InSquare (-81/640) (241/640) (1/640) tau := by
                    convert childLR hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3331.sound htau (by
                    simp only [Batch0416.cell3331, Batch0416.tau3331, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232111 (by positivity) using 1 <;> norm_num)
                · have hs23232113 : InSquare (-81/640) (243/640) (1/640) tau := by
                    convert childUR hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3333.sound htau (by
                    simp only [Batch0416.cell3333, Batch0416.tau3333, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232113 (by positivity) using 1 <;> norm_num)
            · have hs2323213 : InSquare (-41/320) (123/320) (1/320) tau := by
                convert childUR hs232321 hx232321 hy232321 using 1 <;> norm_num
              exact (outside_2323213 htau hs2323213).elim
        · have hs232323 : InSquare (-21/160) (63/160) (1/160) tau := by
            convert childUR hs23232 hx23232 hy23232 using 1 <;> norm_num
          exact (outside_232323 htau hs232323).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2323 | hy2323
    · have hs23231 : InSquare (-9/80) (29/80) (1/80) tau := by
        convert childLR hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23231 | hx23231
      · rcases le_total tau.im (29/80 : ℝ) with hy23231 | hy23231
        · have hs232310 : InSquare (-19/160) (57/160) (1/160) tau := by
            convert childLL hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232310 | hx232310
          · rcases le_total tau.im (57/160 : ℝ) with hy232310 | hy232310
            · have hs2323100 : InSquare (-39/320) (113/320) (1/320) tau := by
                convert childLL hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2123.sound htau (by
                simp only [Batch0265.cell2123, Batch0265.tau2123, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323100 (by positivity) using 1 <;> norm_num)
            · have hs2323102 : InSquare (-39/320) (23/64) (1/320) tau := by
                convert childUL hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2125.sound htau (by
                simp only [Batch0265.cell2125, Batch0265.tau2125, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232310 | hy232310
            · have hs2323101 : InSquare (-37/320) (113/320) (1/320) tau := by
                convert childLR hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2124.sound htau (by
                simp only [Batch0265.cell2124, Batch0265.tau2124, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323101 (by positivity) using 1 <;> norm_num)
            · have hs2323103 : InSquare (-37/320) (23/64) (1/320) tau := by
                convert childUR hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2126.sound htau (by
                simp only [Batch0265.cell2126, Batch0265.tau2126, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323103 (by positivity) using 1 <;> norm_num)
        · have hs232312 : InSquare (-19/160) (59/160) (1/160) tau := by
            convert childUL hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232312 | hx232312
          · rcases le_total tau.im (59/160 : ℝ) with hy232312 | hy232312
            · have hs2323120 : InSquare (-39/320) (117/320) (1/320) tau := by
                convert childLL hs232312 hx232312 hy232312 using 1 <;> norm_num
              exact Batch0266.cell2131.sound htau (by
                simp only [Batch0266.cell2131, Batch0266.tau2131, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323120 (by positivity) using 1 <;> norm_num)
            · have hs2323122 : InSquare (-39/320) (119/320) (1/320) tau := by
                convert childUL hs232312 hx232312 hy232312 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323122 | hx2323122
              · rcases le_total tau.im (119/320 : ℝ) with hy2323122 | hy2323122
                · have hs23231220 : InSquare (-79/640) (237/640) (1/640) tau := by
                    convert childLL hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0413.cell3311.sound htau (by
                    simp only [Batch0413.cell3311, Batch0413.tau3311, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231220 (by positivity) using 1 <;> norm_num)
                · have hs23231222 : InSquare (-79/640) (239/640) (1/640) tau := by
                    convert childUL hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3313.sound htau (by
                    simp only [Batch0414.cell3313, Batch0414.tau3313, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323122 | hy2323122
                · have hs23231221 : InSquare (-77/640) (237/640) (1/640) tau := by
                    convert childLR hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3312.sound htau (by
                    simp only [Batch0414.cell3312, Batch0414.tau3312, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231221 (by positivity) using 1 <;> norm_num)
                · have hs23231223 : InSquare (-77/640) (239/640) (1/640) tau := by
                    convert childUR hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3314.sound htau (by
                    simp only [Batch0414.cell3314, Batch0414.tau3314, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232312 | hy232312
            · have hs2323121 : InSquare (-37/320) (117/320) (1/320) tau := by
                convert childLR hs232312 hx232312 hy232312 using 1 <;> norm_num
              exact Batch0266.cell2132.sound htau (by
                simp only [Batch0266.cell2132, Batch0266.tau2132, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323121 (by positivity) using 1 <;> norm_num)
            · have hs2323123 : InSquare (-37/320) (119/320) (1/320) tau := by
                convert childUR hs232312 hx232312 hy232312 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323123 | hx2323123
              · rcases le_total tau.im (119/320 : ℝ) with hy2323123 | hy2323123
                · have hs23231230 : InSquare (-15/128) (237/640) (1/640) tau := by
                    convert childLL hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3315.sound htau (by
                    simp only [Batch0414.cell3315, Batch0414.tau3315, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231230 (by positivity) using 1 <;> norm_num)
                · have hs23231232 : InSquare (-15/128) (239/640) (1/640) tau := by
                    convert childUL hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3317.sound htau (by
                    simp only [Batch0414.cell3317, Batch0414.tau3317, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323123 | hy2323123
                · have hs23231231 : InSquare (-73/640) (237/640) (1/640) tau := by
                    convert childLR hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3316.sound htau (by
                    simp only [Batch0414.cell3316, Batch0414.tau3316, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231231 (by positivity) using 1 <;> norm_num)
                · have hs23231233 : InSquare (-73/640) (239/640) (1/640) tau := by
                    convert childUR hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3318.sound htau (by
                    simp only [Batch0414.cell3318, Batch0414.tau3318, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23231 | hy23231
        · have hs232311 : InSquare (-17/160) (57/160) (1/160) tau := by
            convert childLR hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232311 | hx232311
          · rcases le_total tau.im (57/160 : ℝ) with hy232311 | hy232311
            · have hs2323110 : InSquare (-7/64) (113/320) (1/320) tau := by
                convert childLL hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0265.cell2127.sound htau (by
                simp only [Batch0265.cell2127, Batch0265.tau2127, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323110 (by positivity) using 1 <;> norm_num)
            · have hs2323112 : InSquare (-7/64) (23/64) (1/320) tau := by
                convert childUL hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2129.sound htau (by
                simp only [Batch0266.cell2129, Batch0266.tau2129, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232311 | hy232311
            · have hs2323111 : InSquare (-33/320) (113/320) (1/320) tau := by
                convert childLR hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2128.sound htau (by
                simp only [Batch0266.cell2128, Batch0266.tau2128, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323111 (by positivity) using 1 <;> norm_num)
            · have hs2323113 : InSquare (-33/320) (23/64) (1/320) tau := by
                convert childUR hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2130.sound htau (by
                simp only [Batch0266.cell2130, Batch0266.tau2130, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323113 (by positivity) using 1 <;> norm_num)
        · have hs232313 : InSquare (-17/160) (59/160) (1/160) tau := by
            convert childUR hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232313 | hx232313
          · rcases le_total tau.im (59/160 : ℝ) with hy232313 | hy232313
            · have hs2323130 : InSquare (-7/64) (117/320) (1/320) tau := by
                convert childLL hs232313 hx232313 hy232313 using 1 <;> norm_num
              exact Batch0266.cell2133.sound htau (by
                simp only [Batch0266.cell2133, Batch0266.tau2133, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323130 (by positivity) using 1 <;> norm_num)
            · have hs2323132 : InSquare (-7/64) (119/320) (1/320) tau := by
                convert childUL hs232313 hx232313 hy232313 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323132 | hx2323132
              · rcases le_total tau.im (119/320 : ℝ) with hy2323132 | hy2323132
                · have hs23231320 : InSquare (-71/640) (237/640) (1/640) tau := by
                    convert childLL hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0414.cell3319.sound htau (by
                    simp only [Batch0414.cell3319, Batch0414.tau3319, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231320 (by positivity) using 1 <;> norm_num)
                · have hs23231322 : InSquare (-71/640) (239/640) (1/640) tau := by
                    convert childUL hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3321.sound htau (by
                    simp only [Batch0415.cell3321, Batch0415.tau3321, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323132 | hy2323132
                · have hs23231321 : InSquare (-69/640) (237/640) (1/640) tau := by
                    convert childLR hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3320.sound htau (by
                    simp only [Batch0415.cell3320, Batch0415.tau3320, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231321 (by positivity) using 1 <;> norm_num)
                · have hs23231323 : InSquare (-69/640) (239/640) (1/640) tau := by
                    convert childUR hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3322.sound htau (by
                    simp only [Batch0415.cell3322, Batch0415.tau3322, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232313 | hy232313
            · have hs2323131 : InSquare (-33/320) (117/320) (1/320) tau := by
                convert childLR hs232313 hx232313 hy232313 using 1 <;> norm_num
              exact Batch0266.cell2134.sound htau (by
                simp only [Batch0266.cell2134, Batch0266.tau2134, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323131 (by positivity) using 1 <;> norm_num)
            · have hs2323133 : InSquare (-33/320) (119/320) (1/320) tau := by
                convert childUR hs232313 hx232313 hy232313 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323133 | hx2323133
              · rcases le_total tau.im (119/320 : ℝ) with hy2323133 | hy2323133
                · have hs23231330 : InSquare (-67/640) (237/640) (1/640) tau := by
                    convert childLL hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3323.sound htau (by
                    simp only [Batch0415.cell3323, Batch0415.tau3323, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231330 (by positivity) using 1 <;> norm_num)
                · have hs23231332 : InSquare (-67/640) (239/640) (1/640) tau := by
                    convert childUL hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3325.sound htau (by
                    simp only [Batch0415.cell3325, Batch0415.tau3325, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323133 | hy2323133
                · have hs23231331 : InSquare (-13/128) (237/640) (1/640) tau := by
                    convert childLR hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3324.sound htau (by
                    simp only [Batch0415.cell3324, Batch0415.tau3324, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231331 (by positivity) using 1 <;> norm_num)
                · have hs23231333 : InSquare (-13/128) (239/640) (1/640) tau := by
                    convert childUR hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3326.sound htau (by
                    simp only [Batch0415.cell3326, Batch0415.tau3326, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231333 (by positivity) using 1 <;> norm_num)
    · have hs23233 : InSquare (-9/80) (31/80) (1/80) tau := by
        convert childUR hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23233 | hx23233
      · rcases le_total tau.im (31/80 : ℝ) with hy23233 | hy23233
        · have hs232330 : InSquare (-19/160) (61/160) (1/160) tau := by
            convert childLL hs23233 hx23233 hy23233 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232330 | hx232330
          · rcases le_total tau.im (61/160 : ℝ) with hy232330 | hy232330
            · have hs2323300 : InSquare (-39/320) (121/320) (1/320) tau := by
                convert childLL hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323300 | hx2323300
              · rcases le_total tau.im (121/320 : ℝ) with hy2323300 | hy2323300
                · have hs23233000 : InSquare (-79/640) (241/640) (1/640) tau := by
                    convert childLL hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0416.cell3334.sound htau (by
                    simp only [Batch0416.cell3334, Batch0416.tau3334, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233000 (by positivity) using 1 <;> norm_num)
                · have hs23233002 : InSquare (-79/640) (243/640) (1/640) tau := by
                    convert childUL hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0417.cell3336.sound htau (by
                    simp only [Batch0417.cell3336, Batch0417.tau3336, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323300 | hy2323300
                · have hs23233001 : InSquare (-77/640) (241/640) (1/640) tau := by
                    convert childLR hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0416.cell3335.sound htau (by
                    simp only [Batch0416.cell3335, Batch0416.tau3335, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233001 (by positivity) using 1 <;> norm_num)
                · have hs23233003 : InSquare (-77/640) (243/640) (1/640) tau := by
                    convert childUR hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0417.cell3337.sound htau (by
                    simp only [Batch0417.cell3337, Batch0417.tau3337, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233003 (by positivity) using 1 <;> norm_num)
            · have hs2323302 : InSquare (-39/320) (123/320) (1/320) tau := by
                convert childUL hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323302 | hx2323302
              · rcases le_total tau.im (123/320 : ℝ) with hy2323302 | hy2323302
                · have hs23233020 : InSquare (-79/640) (49/128) (1/640) tau := by
                    convert childLL hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233020 htau hs23233020).elim
                · have hs23233022 : InSquare (-79/640) (247/640) (1/640) tau := by
                    convert childUL hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233022 htau hs23233022).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy2323302 | hy2323302
                · have hs23233021 : InSquare (-77/640) (49/128) (1/640) tau := by
                    convert childLR hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact Batch0417.cell3342.sound htau (by
                    simp only [Batch0417.cell3342, Batch0417.tau3342, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233021 (by positivity) using 1 <;> norm_num)
                · have hs23233023 : InSquare (-77/640) (247/640) (1/640) tau := by
                    convert childUR hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233023 htau hs23233023).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232330 | hy232330
            · have hs2323301 : InSquare (-37/320) (121/320) (1/320) tau := by
                convert childLR hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323301 | hx2323301
              · rcases le_total tau.im (121/320 : ℝ) with hy2323301 | hy2323301
                · have hs23233010 : InSquare (-15/128) (241/640) (1/640) tau := by
                    convert childLL hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3338.sound htau (by
                    simp only [Batch0417.cell3338, Batch0417.tau3338, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233010 (by positivity) using 1 <;> norm_num)
                · have hs23233012 : InSquare (-15/128) (243/640) (1/640) tau := by
                    convert childUL hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3340.sound htau (by
                    simp only [Batch0417.cell3340, Batch0417.tau3340, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323301 | hy2323301
                · have hs23233011 : InSquare (-73/640) (241/640) (1/640) tau := by
                    convert childLR hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3339.sound htau (by
                    simp only [Batch0417.cell3339, Batch0417.tau3339, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233011 (by positivity) using 1 <;> norm_num)
                · have hs23233013 : InSquare (-73/640) (243/640) (1/640) tau := by
                    convert childUR hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3341.sound htau (by
                    simp only [Batch0417.cell3341, Batch0417.tau3341, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233013 (by positivity) using 1 <;> norm_num)
            · have hs2323303 : InSquare (-37/320) (123/320) (1/320) tau := by
                convert childUR hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323303 | hx2323303
              · rcases le_total tau.im (123/320 : ℝ) with hy2323303 | hy2323303
                · have hs23233030 : InSquare (-15/128) (49/128) (1/640) tau := by
                    convert childLL hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact Batch0417.cell3343.sound htau (by
                    simp only [Batch0417.cell3343, Batch0417.tau3343, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233030 (by positivity) using 1 <;> norm_num)
                · have hs23233032 : InSquare (-15/128) (247/640) (1/640) tau := by
                    convert childUL hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact (outside_23233032 htau hs23233032).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy2323303 | hy2323303
                · have hs23233031 : InSquare (-73/640) (49/128) (1/640) tau := by
                    convert childLR hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact Batch0418.cell3344.sound htau (by
                    simp only [Batch0418.cell3344, Batch0418.tau3344, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233031 (by positivity) using 1 <;> norm_num)
                · have hs23233033 : InSquare (-73/640) (247/640) (1/640) tau := by
                    convert childUR hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact (outside_23233033 htau hs23233033).elim
        · have hs232332 : InSquare (-19/160) (63/160) (1/160) tau := by
            convert childUL hs23233 hx23233 hy23233 using 1 <;> norm_num
          exact (outside_232332 htau hs232332).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23233 | hy23233
        · have hs232331 : InSquare (-17/160) (61/160) (1/160) tau := by
            convert childLR hs23233 hx23233 hy23233 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232331 | hx232331
          · rcases le_total tau.im (61/160 : ℝ) with hy232331 | hy232331
            · have hs2323310 : InSquare (-7/64) (121/320) (1/320) tau := by
                convert childLL hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323310 | hx2323310
              · rcases le_total tau.im (121/320 : ℝ) with hy2323310 | hy2323310
                · have hs23233100 : InSquare (-71/640) (241/640) (1/640) tau := by
                    convert childLL hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3345.sound htau (by
                    simp only [Batch0418.cell3345, Batch0418.tau3345, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233100 (by positivity) using 1 <;> norm_num)
                · have hs23233102 : InSquare (-71/640) (243/640) (1/640) tau := by
                    convert childUL hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3347.sound htau (by
                    simp only [Batch0418.cell3347, Batch0418.tau3347, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323310 | hy2323310
                · have hs23233101 : InSquare (-69/640) (241/640) (1/640) tau := by
                    convert childLR hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3346.sound htau (by
                    simp only [Batch0418.cell3346, Batch0418.tau3346, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233101 (by positivity) using 1 <;> norm_num)
                · have hs23233103 : InSquare (-69/640) (243/640) (1/640) tau := by
                    convert childUR hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3348.sound htau (by
                    simp only [Batch0418.cell3348, Batch0418.tau3348, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233103 (by positivity) using 1 <;> norm_num)
            · have hs2323312 : InSquare (-7/64) (123/320) (1/320) tau := by
                convert childUL hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323312 | hx2323312
              · rcases le_total tau.im (123/320 : ℝ) with hy2323312 | hy2323312
                · have hs23233120 : InSquare (-71/640) (49/128) (1/640) tau := by
                    convert childLL hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3353.sound htau (by
                    simp only [Batch0419.cell3353, Batch0419.tau3353, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233120 (by positivity) using 1 <;> norm_num)
                · have hs23233122 : InSquare (-71/640) (247/640) (1/640) tau := by
                    convert childUL hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3355.sound htau (by
                    simp only [Batch0419.cell3355, Batch0419.tau3355, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2323312 | hy2323312
                · have hs23233121 : InSquare (-69/640) (49/128) (1/640) tau := by
                    convert childLR hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3354.sound htau (by
                    simp only [Batch0419.cell3354, Batch0419.tau3354, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233121 (by positivity) using 1 <;> norm_num)
                · have hs23233123 : InSquare (-69/640) (247/640) (1/640) tau := by
                    convert childUR hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3356.sound htau (by
                    simp only [Batch0419.cell3356, Batch0419.tau3356, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy232331 | hy232331
            · have hs2323311 : InSquare (-33/320) (121/320) (1/320) tau := by
                convert childLR hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323311 | hx2323311
              · rcases le_total tau.im (121/320 : ℝ) with hy2323311 | hy2323311
                · have hs23233110 : InSquare (-67/640) (241/640) (1/640) tau := by
                    convert childLL hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3349.sound htau (by
                    simp only [Batch0418.cell3349, Batch0418.tau3349, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233110 (by positivity) using 1 <;> norm_num)
                · have hs23233112 : InSquare (-67/640) (243/640) (1/640) tau := by
                    convert childUL hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3351.sound htau (by
                    simp only [Batch0418.cell3351, Batch0418.tau3351, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323311 | hy2323311
                · have hs23233111 : InSquare (-13/128) (241/640) (1/640) tau := by
                    convert childLR hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3350.sound htau (by
                    simp only [Batch0418.cell3350, Batch0418.tau3350, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233111 (by positivity) using 1 <;> norm_num)
                · have hs23233113 : InSquare (-13/128) (243/640) (1/640) tau := by
                    convert childUR hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0419.cell3352.sound htau (by
                    simp only [Batch0419.cell3352, Batch0419.tau3352, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233113 (by positivity) using 1 <;> norm_num)
            · have hs2323313 : InSquare (-33/320) (123/320) (1/320) tau := by
                convert childUR hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323313 | hx2323313
              · rcases le_total tau.im (123/320 : ℝ) with hy2323313 | hy2323313
                · have hs23233130 : InSquare (-67/640) (49/128) (1/640) tau := by
                    convert childLL hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3357.sound htau (by
                    simp only [Batch0419.cell3357, Batch0419.tau3357, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233130 (by positivity) using 1 <;> norm_num)
                · have hs23233132 : InSquare (-67/640) (247/640) (1/640) tau := by
                    convert childUL hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3359.sound htau (by
                    simp only [Batch0419.cell3359, Batch0419.tau3359, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2323313 | hy2323313
                · have hs23233131 : InSquare (-13/128) (49/128) (1/640) tau := by
                    convert childLR hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3358.sound htau (by
                    simp only [Batch0419.cell3358, Batch0419.tau3358, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233131 (by positivity) using 1 <;> norm_num)
                · have hs23233133 : InSquare (-13/128) (247/640) (1/640) tau := by
                    convert childUR hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0420.cell3360.sound htau (by
                    simp only [Batch0420.cell3360, Batch0420.tau3360, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233133 (by positivity) using 1 <;> norm_num)
        · have hs232333 : InSquare (-17/160) (63/160) (1/160) tau := by
            convert childUR hs23233 hx23233 hy23233 using 1 <;> norm_num
          exact (outside_232333 htau hs232333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2330 | hx2330
  · rcases le_total tau.im (13/40 : ℝ) with hy2330 | hy2330
    · have hs23300 : InSquare (-7/80) (5/16) (1/80) tau := by
        convert childLL hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23300 | hx23300
      · rcases le_total tau.im (5/16 : ℝ) with hy23300 | hy23300
        · have hs233000 : InSquare (-3/32) (49/160) (1/160) tau := by
            convert childLL hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0956.sound htau (by
            simp only [Batch0119.cell0956, Batch0119.tau0956, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233000 (by positivity) using 1 <;> norm_num)
        · have hs233002 : InSquare (-3/32) (51/160) (1/160) tau := by
            convert childUL hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0958.sound htau (by
            simp only [Batch0119.cell0958, Batch0119.tau0958, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23300 | hy23300
        · have hs233001 : InSquare (-13/160) (49/160) (1/160) tau := by
            convert childLR hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0957.sound htau (by
            simp only [Batch0119.cell0957, Batch0119.tau0957, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233001 (by positivity) using 1 <;> norm_num)
        · have hs233003 : InSquare (-13/160) (51/160) (1/160) tau := by
            convert childUR hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0959.sound htau (by
            simp only [Batch0119.cell0959, Batch0119.tau0959, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233003 (by positivity) using 1 <;> norm_num)
    · have hs23302 : InSquare (-7/80) (27/80) (1/80) tau := by
        convert childUL hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23302 | hx23302
      · rcases le_total tau.im (27/80 : ℝ) with hy23302 | hy23302
        · have hs233020 : InSquare (-3/32) (53/160) (1/160) tau := by
            convert childLL hs23302 hx23302 hy23302 using 1 <;> norm_num
          exact Batch0120.cell0964.sound htau (by
            simp only [Batch0120.cell0964, Batch0120.tau0964, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233020 (by positivity) using 1 <;> norm_num)
        · have hs233022 : InSquare (-3/32) (11/32) (1/160) tau := by
            convert childUL hs23302 hx23302 hy23302 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233022 | hx233022
          · rcases le_total tau.im (11/32 : ℝ) with hy233022 | hy233022
            · have hs2330220 : InSquare (-31/320) (109/320) (1/320) tau := by
                convert childLL hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0266.cell2135.sound htau (by
                simp only [Batch0266.cell2135, Batch0266.tau2135, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330220 (by positivity) using 1 <;> norm_num)
            · have hs2330222 : InSquare (-31/320) (111/320) (1/320) tau := by
                convert childUL hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2137.sound htau (by
                simp only [Batch0267.cell2137, Batch0267.tau2137, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233022 | hy233022
            · have hs2330221 : InSquare (-29/320) (109/320) (1/320) tau := by
                convert childLR hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2136.sound htau (by
                simp only [Batch0267.cell2136, Batch0267.tau2136, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330221 (by positivity) using 1 <;> norm_num)
            · have hs2330223 : InSquare (-29/320) (111/320) (1/320) tau := by
                convert childUR hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2138.sound htau (by
                simp only [Batch0267.cell2138, Batch0267.tau2138, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23302 | hy23302
        · have hs233021 : InSquare (-13/160) (53/160) (1/160) tau := by
            convert childLR hs23302 hx23302 hy23302 using 1 <;> norm_num
          exact Batch0120.cell0965.sound htau (by
            simp only [Batch0120.cell0965, Batch0120.tau0965, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233021 (by positivity) using 1 <;> norm_num)
        · have hs233023 : InSquare (-13/160) (11/32) (1/160) tau := by
            convert childUR hs23302 hx23302 hy23302 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233023 | hx233023
          · rcases le_total tau.im (11/32 : ℝ) with hy233023 | hy233023
            · have hs2330230 : InSquare (-27/320) (109/320) (1/320) tau := by
                convert childLL hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2139.sound htau (by
                simp only [Batch0267.cell2139, Batch0267.tau2139, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330230 (by positivity) using 1 <;> norm_num)
            · have hs2330232 : InSquare (-27/320) (111/320) (1/320) tau := by
                convert childUL hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2141.sound htau (by
                simp only [Batch0267.cell2141, Batch0267.tau2141, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233023 | hy233023
            · have hs2330231 : InSquare (-5/64) (109/320) (1/320) tau := by
                convert childLR hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2140.sound htau (by
                simp only [Batch0267.cell2140, Batch0267.tau2140, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330231 (by positivity) using 1 <;> norm_num)
            · have hs2330233 : InSquare (-5/64) (111/320) (1/320) tau := by
                convert childUR hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2142.sound htau (by
                simp only [Batch0267.cell2142, Batch0267.tau2142, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2330 | hy2330
    · have hs23301 : InSquare (-1/16) (5/16) (1/80) tau := by
        convert childLR hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23301 | hx23301
      · rcases le_total tau.im (5/16 : ℝ) with hy23301 | hy23301
        · have hs233010 : InSquare (-11/160) (49/160) (1/160) tau := by
            convert childLL hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0960.sound htau (by
            simp only [Batch0120.cell0960, Batch0120.tau0960, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233010 (by positivity) using 1 <;> norm_num)
        · have hs233012 : InSquare (-11/160) (51/160) (1/160) tau := by
            convert childUL hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0962.sound htau (by
            simp only [Batch0120.cell0962, Batch0120.tau0962, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23301 | hy23301
        · have hs233011 : InSquare (-9/160) (49/160) (1/160) tau := by
            convert childLR hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0961.sound htau (by
            simp only [Batch0120.cell0961, Batch0120.tau0961, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233011 (by positivity) using 1 <;> norm_num)
        · have hs233013 : InSquare (-9/160) (51/160) (1/160) tau := by
            convert childUR hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0963.sound htau (by
            simp only [Batch0120.cell0963, Batch0120.tau0963, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233013 (by positivity) using 1 <;> norm_num)
    · have hs23303 : InSquare (-1/16) (27/80) (1/80) tau := by
        convert childUR hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23303 | hx23303
      · rcases le_total tau.im (27/80 : ℝ) with hy23303 | hy23303
        · have hs233030 : InSquare (-11/160) (53/160) (1/160) tau := by
            convert childLL hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0120.cell0966.sound htau (by
            simp only [Batch0120.cell0966, Batch0120.tau0966, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233030 (by positivity) using 1 <;> norm_num)
        · have hs233032 : InSquare (-11/160) (11/32) (1/160) tau := by
            convert childUL hs23303 hx23303 hy23303 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233032 | hx233032
          · rcases le_total tau.im (11/32 : ℝ) with hy233032 | hy233032
            · have hs2330320 : InSquare (-23/320) (109/320) (1/320) tau := by
                convert childLL hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0267.cell2143.sound htau (by
                simp only [Batch0267.cell2143, Batch0267.tau2143, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330320 (by positivity) using 1 <;> norm_num)
            · have hs2330322 : InSquare (-23/320) (111/320) (1/320) tau := by
                convert childUL hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2145.sound htau (by
                simp only [Batch0268.cell2145, Batch0268.tau2145, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233032 | hy233032
            · have hs2330321 : InSquare (-21/320) (109/320) (1/320) tau := by
                convert childLR hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2144.sound htau (by
                simp only [Batch0268.cell2144, Batch0268.tau2144, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330321 (by positivity) using 1 <;> norm_num)
            · have hs2330323 : InSquare (-21/320) (111/320) (1/320) tau := by
                convert childUR hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2146.sound htau (by
                simp only [Batch0268.cell2146, Batch0268.tau2146, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23303 | hy23303
        · have hs233031 : InSquare (-9/160) (53/160) (1/160) tau := by
            convert childLR hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0120.cell0967.sound htau (by
            simp only [Batch0120.cell0967, Batch0120.tau0967, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233031 (by positivity) using 1 <;> norm_num)
        · have hs233033 : InSquare (-9/160) (11/32) (1/160) tau := by
            convert childUR hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0121.cell0968.sound htau (by
            simp only [Batch0121.cell0968, Batch0121.tau0968, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2331 | hx2331
  · rcases le_total tau.im (13/40 : ℝ) with hy2331 | hy2331
    · have hs23310 : InSquare (-3/80) (5/16) (1/80) tau := by
        convert childLL hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23310 | hx23310
      · rcases le_total tau.im (5/16 : ℝ) with hy23310 | hy23310
        · have hs233100 : InSquare (-7/160) (49/160) (1/160) tau := by
            convert childLL hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0969.sound htau (by
            simp only [Batch0121.cell0969, Batch0121.tau0969, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233100 (by positivity) using 1 <;> norm_num)
        · have hs233102 : InSquare (-7/160) (51/160) (1/160) tau := by
            convert childUL hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0971.sound htau (by
            simp only [Batch0121.cell0971, Batch0121.tau0971, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23310 | hy23310
        · have hs233101 : InSquare (-1/32) (49/160) (1/160) tau := by
            convert childLR hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0970.sound htau (by
            simp only [Batch0121.cell0970, Batch0121.tau0970, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233101 (by positivity) using 1 <;> norm_num)
        · have hs233103 : InSquare (-1/32) (51/160) (1/160) tau := by
            convert childUR hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0972.sound htau (by
            simp only [Batch0121.cell0972, Batch0121.tau0972, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233103 (by positivity) using 1 <;> norm_num)
    · have hs23312 : InSquare (-3/80) (27/80) (1/80) tau := by
        convert childUL hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23312 | hx23312
      · rcases le_total tau.im (27/80 : ℝ) with hy23312 | hy23312
        · have hs233120 : InSquare (-7/160) (53/160) (1/160) tau := by
            convert childLL hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0977.sound htau (by
            simp only [Batch0122.cell0977, Batch0122.tau0977, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233120 (by positivity) using 1 <;> norm_num)
        · have hs233122 : InSquare (-7/160) (11/32) (1/160) tau := by
            convert childUL hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0979.sound htau (by
            simp only [Batch0122.cell0979, Batch0122.tau0979, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23312 | hy23312
        · have hs233121 : InSquare (-1/32) (53/160) (1/160) tau := by
            convert childLR hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0978.sound htau (by
            simp only [Batch0122.cell0978, Batch0122.tau0978, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233121 (by positivity) using 1 <;> norm_num)
        · have hs233123 : InSquare (-1/32) (11/32) (1/160) tau := by
            convert childUR hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0980.sound htau (by
            simp only [Batch0122.cell0980, Batch0122.tau0980, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2331 | hy2331
    · have hs23311 : InSquare (-1/80) (5/16) (1/80) tau := by
        convert childLR hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23311 | hx23311
      · rcases le_total tau.im (5/16 : ℝ) with hy23311 | hy23311
        · have hs233110 : InSquare (-3/160) (49/160) (1/160) tau := by
            convert childLL hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0973.sound htau (by
            simp only [Batch0121.cell0973, Batch0121.tau0973, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233110 (by positivity) using 1 <;> norm_num)
        · have hs233112 : InSquare (-3/160) (51/160) (1/160) tau := by
            convert childUL hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0975.sound htau (by
            simp only [Batch0121.cell0975, Batch0121.tau0975, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23311 | hy23311
        · have hs233111 : InSquare (-1/160) (49/160) (1/160) tau := by
            convert childLR hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0974.sound htau (by
            simp only [Batch0121.cell0974, Batch0121.tau0974, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233111 (by positivity) using 1 <;> norm_num)
        · have hs233113 : InSquare (-1/160) (51/160) (1/160) tau := by
            convert childUR hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0122.cell0976.sound htau (by
            simp only [Batch0122.cell0976, Batch0122.tau0976, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233113 (by positivity) using 1 <;> norm_num)
    · have hs23313 : InSquare (-1/80) (27/80) (1/80) tau := by
        convert childUR hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23313 | hx23313
      · rcases le_total tau.im (27/80 : ℝ) with hy23313 | hy23313
        · have hs233130 : InSquare (-3/160) (53/160) (1/160) tau := by
            convert childLL hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0981.sound htau (by
            simp only [Batch0122.cell0981, Batch0122.tau0981, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233130 (by positivity) using 1 <;> norm_num)
        · have hs233132 : InSquare (-3/160) (11/32) (1/160) tau := by
            convert childUL hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0983.sound htau (by
            simp only [Batch0122.cell0983, Batch0122.tau0983, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23313 | hy23313
        · have hs233131 : InSquare (-1/160) (53/160) (1/160) tau := by
            convert childLR hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0982.sound htau (by
            simp only [Batch0122.cell0982, Batch0122.tau0982, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233131 (by positivity) using 1 <;> norm_num)
        · have hs233133 : InSquare (-1/160) (11/32) (1/160) tau := by
            convert childUR hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0123.cell0984.sound htau (by
            simp only [Batch0123.cell0984, Batch0123.tau0984, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331

end


