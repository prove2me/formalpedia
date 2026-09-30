-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3223__4
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3223__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:16:41.570784+00:00
-- url     : https://prove2.me/theorems/5dc438ad-544b-43ae-9b9e-022a1139d435
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3223 (+3 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3230, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3231, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3232).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0284
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0285
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0286
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0287
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0288
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0451
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0452
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0455
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0456
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0458
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0459
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0142
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0289
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0290
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0291
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0292
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0296
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0298
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0299
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0461
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0300
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0302
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0462
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0463
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0465
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0466
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0470
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0471
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0472

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_3223322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/64) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (33/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (57/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3223 | hx3223
  · rcases le_total tau.im (3/8 : ℝ) with hy3223 | hy3223
    · have hs32230 : InSquare (1/16) (29/80) (1/80) tau := by
        convert childLL hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32230 | hx32230
      · rcases le_total tau.im (29/80 : ℝ) with hy32230 | hy32230
        · have hs322300 : InSquare (9/160) (57/160) (1/160) tau := by
            convert childLL hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322300 | hx322300
          · rcases le_total tau.im (57/160 : ℝ) with hy322300 | hy322300
            · have hs3223000 : InSquare (17/320) (113/320) (1/320) tau := by
                convert childLL hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2277.sound htau (by
                simp only [Batch0284.cell2277, Batch0284.tau2277, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223000 (by positivity) using 1 <;> norm_num)
            · have hs3223002 : InSquare (17/320) (23/64) (1/320) tau := by
                convert childUL hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2279.sound htau (by
                simp only [Batch0284.cell2279, Batch0284.tau2279, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322300 | hy322300
            · have hs3223001 : InSquare (19/320) (113/320) (1/320) tau := by
                convert childLR hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2278.sound htau (by
                simp only [Batch0284.cell2278, Batch0284.tau2278, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223001 (by positivity) using 1 <;> norm_num)
            · have hs3223003 : InSquare (19/320) (23/64) (1/320) tau := by
                convert childUR hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0285.cell2280.sound htau (by
                simp only [Batch0285.cell2280, Batch0285.tau2280, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223003 (by positivity) using 1 <;> norm_num)
        · have hs322302 : InSquare (9/160) (59/160) (1/160) tau := by
            convert childUL hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322302 | hx322302
          · rcases le_total tau.im (59/160 : ℝ) with hy322302 | hy322302
            · have hs3223020 : InSquare (17/320) (117/320) (1/320) tau := by
                convert childLL hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2285.sound htau (by
                simp only [Batch0285.cell2285, Batch0285.tau2285, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223020 (by positivity) using 1 <;> norm_num)
            · have hs3223022 : InSquare (17/320) (119/320) (1/320) tau := by
                convert childUL hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2287.sound htau (by
                simp only [Batch0285.cell2287, Batch0285.tau2287, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322302 | hy322302
            · have hs3223021 : InSquare (19/320) (117/320) (1/320) tau := by
                convert childLR hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2286.sound htau (by
                simp only [Batch0285.cell2286, Batch0285.tau2286, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223021 (by positivity) using 1 <;> norm_num)
            · have hs3223023 : InSquare (19/320) (119/320) (1/320) tau := by
                convert childUR hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0286.cell2288.sound htau (by
                simp only [Batch0286.cell2288, Batch0286.tau2288, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32230 | hy32230
        · have hs322301 : InSquare (11/160) (57/160) (1/160) tau := by
            convert childLR hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322301 | hx322301
          · rcases le_total tau.im (57/160 : ℝ) with hy322301 | hy322301
            · have hs3223010 : InSquare (21/320) (113/320) (1/320) tau := by
                convert childLL hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2281.sound htau (by
                simp only [Batch0285.cell2281, Batch0285.tau2281, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223010 (by positivity) using 1 <;> norm_num)
            · have hs3223012 : InSquare (21/320) (23/64) (1/320) tau := by
                convert childUL hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2283.sound htau (by
                simp only [Batch0285.cell2283, Batch0285.tau2283, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322301 | hy322301
            · have hs3223011 : InSquare (23/320) (113/320) (1/320) tau := by
                convert childLR hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2282.sound htau (by
                simp only [Batch0285.cell2282, Batch0285.tau2282, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223011 (by positivity) using 1 <;> norm_num)
            · have hs3223013 : InSquare (23/320) (23/64) (1/320) tau := by
                convert childUR hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2284.sound htau (by
                simp only [Batch0285.cell2284, Batch0285.tau2284, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223013 (by positivity) using 1 <;> norm_num)
        · have hs322303 : InSquare (11/160) (59/160) (1/160) tau := by
            convert childUR hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322303 | hx322303
          · rcases le_total tau.im (59/160 : ℝ) with hy322303 | hy322303
            · have hs3223030 : InSquare (21/320) (117/320) (1/320) tau := by
                convert childLL hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2289.sound htau (by
                simp only [Batch0286.cell2289, Batch0286.tau2289, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223030 (by positivity) using 1 <;> norm_num)
            · have hs3223032 : InSquare (21/320) (119/320) (1/320) tau := by
                convert childUL hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2291.sound htau (by
                simp only [Batch0286.cell2291, Batch0286.tau2291, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322303 | hy322303
            · have hs3223031 : InSquare (23/320) (117/320) (1/320) tau := by
                convert childLR hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2290.sound htau (by
                simp only [Batch0286.cell2290, Batch0286.tau2290, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223031 (by positivity) using 1 <;> norm_num)
            · have hs3223033 : InSquare (23/320) (119/320) (1/320) tau := by
                convert childUR hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2292.sound htau (by
                simp only [Batch0286.cell2292, Batch0286.tau2292, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223033 (by positivity) using 1 <;> norm_num)
    · have hs32232 : InSquare (1/16) (31/80) (1/80) tau := by
        convert childUL hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32232 | hx32232
      · rcases le_total tau.im (31/80 : ℝ) with hy32232 | hy32232
        · have hs322320 : InSquare (9/160) (61/160) (1/160) tau := by
            convert childLL hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322320 | hx322320
          · rcases le_total tau.im (61/160 : ℝ) with hy322320 | hy322320
            · have hs3223200 : InSquare (17/320) (121/320) (1/320) tau := by
                convert childLL hs322320 hx322320 hy322320 using 1 <;> norm_num
              exact Batch0288.cell2309.sound htau (by
                simp only [Batch0288.cell2309, Batch0288.tau2309, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223200 (by positivity) using 1 <;> norm_num)
            · have hs3223202 : InSquare (17/320) (123/320) (1/320) tau := by
                convert childUL hs322320 hx322320 hy322320 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223202 | hx3223202
              · rcases le_total tau.im (123/320 : ℝ) with hy3223202 | hy3223202
                · have hs32232020 : InSquare (33/640) (49/128) (1/640) tau := by
                    convert childLL hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3600.sound htau (by
                    simp only [Batch0450.cell3600, Batch0450.tau3600, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232020 (by positivity) using 1 <;> norm_num)
                · have hs32232022 : InSquare (33/640) (247/640) (1/640) tau := by
                    convert childUL hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3602.sound htau (by
                    simp only [Batch0450.cell3602, Batch0450.tau3602, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223202 | hy3223202
                · have hs32232021 : InSquare (7/128) (49/128) (1/640) tau := by
                    convert childLR hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3601.sound htau (by
                    simp only [Batch0450.cell3601, Batch0450.tau3601, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232021 (by positivity) using 1 <;> norm_num)
                · have hs32232023 : InSquare (7/128) (247/640) (1/640) tau := by
                    convert childUR hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3603.sound htau (by
                    simp only [Batch0450.cell3603, Batch0450.tau3603, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322320 | hy322320
            · have hs3223201 : InSquare (19/320) (121/320) (1/320) tau := by
                convert childLR hs322320 hx322320 hy322320 using 1 <;> norm_num
              exact Batch0288.cell2310.sound htau (by
                simp only [Batch0288.cell2310, Batch0288.tau2310, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223201 (by positivity) using 1 <;> norm_num)
            · have hs3223203 : InSquare (19/320) (123/320) (1/320) tau := by
                convert childUR hs322320 hx322320 hy322320 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223203 | hx3223203
              · rcases le_total tau.im (123/320 : ℝ) with hy3223203 | hy3223203
                · have hs32232030 : InSquare (37/640) (49/128) (1/640) tau := by
                    convert childLL hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3604.sound htau (by
                    simp only [Batch0450.cell3604, Batch0450.tau3604, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232030 (by positivity) using 1 <;> norm_num)
                · have hs32232032 : InSquare (37/640) (247/640) (1/640) tau := by
                    convert childUL hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3606.sound htau (by
                    simp only [Batch0450.cell3606, Batch0450.tau3606, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223203 | hy3223203
                · have hs32232031 : InSquare (39/640) (49/128) (1/640) tau := by
                    convert childLR hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3605.sound htau (by
                    simp only [Batch0450.cell3605, Batch0450.tau3605, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232031 (by positivity) using 1 <;> norm_num)
                · have hs32232033 : InSquare (39/640) (247/640) (1/640) tau := by
                    convert childUR hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3607.sound htau (by
                    simp only [Batch0450.cell3607, Batch0450.tau3607, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232033 (by positivity) using 1 <;> norm_num)
        · have hs322322 : InSquare (9/160) (63/160) (1/160) tau := by
            convert childUL hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322322 | hx322322
          · rcases le_total tau.im (63/160 : ℝ) with hy322322 | hy322322
            · have hs3223220 : InSquare (17/320) (25/64) (1/320) tau := by
                convert childLL hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223220 | hx3223220
              · rcases le_total tau.im (25/64 : ℝ) with hy3223220 | hy3223220
                · have hs32232200 : InSquare (33/640) (249/640) (1/640) tau := by
                    convert childLL hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3620.sound htau (by
                    simp only [Batch0452.cell3620, Batch0452.tau3620, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232200 (by positivity) using 1 <;> norm_num)
                · have hs32232202 : InSquare (33/640) (251/640) (1/640) tau := by
                    convert childUL hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3622.sound htau (by
                    simp only [Batch0452.cell3622, Batch0452.tau3622, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223220 | hy3223220
                · have hs32232201 : InSquare (7/128) (249/640) (1/640) tau := by
                    convert childLR hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3621.sound htau (by
                    simp only [Batch0452.cell3621, Batch0452.tau3621, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232201 (by positivity) using 1 <;> norm_num)
                · have hs32232203 : InSquare (7/128) (251/640) (1/640) tau := by
                    convert childUR hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3623.sound htau (by
                    simp only [Batch0452.cell3623, Batch0452.tau3623, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232203 (by positivity) using 1 <;> norm_num)
            · have hs3223222 : InSquare (17/320) (127/320) (1/320) tau := by
                convert childUL hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223222 | hx3223222
              · rcases le_total tau.im (127/320 : ℝ) with hy3223222 | hy3223222
                · have hs32232220 : InSquare (33/640) (253/640) (1/640) tau := by
                    convert childLL hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact Batch0453.cell3628.sound htau (by
                    simp only [Batch0453.cell3628, Batch0453.tau3628, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232220 (by positivity) using 1 <;> norm_num)
                · have hs32232222 : InSquare (33/640) (51/128) (1/640) tau := by
                    convert childUL hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact (outside_32232222 htau hs32232222).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223222 | hy3223222
                · have hs32232221 : InSquare (7/128) (253/640) (1/640) tau := by
                    convert childLR hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact Batch0453.cell3629.sound htau (by
                    simp only [Batch0453.cell3629, Batch0453.tau3629, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232221 (by positivity) using 1 <;> norm_num)
                · have hs32232223 : InSquare (7/128) (51/128) (1/640) tau := by
                    convert childUR hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact (outside_32232223 htau hs32232223).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322322 | hy322322
            · have hs3223221 : InSquare (19/320) (25/64) (1/320) tau := by
                convert childLR hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223221 | hx3223221
              · rcases le_total tau.im (25/64 : ℝ) with hy3223221 | hy3223221
                · have hs32232210 : InSquare (37/640) (249/640) (1/640) tau := by
                    convert childLL hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3624.sound htau (by
                    simp only [Batch0453.cell3624, Batch0453.tau3624, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232210 (by positivity) using 1 <;> norm_num)
                · have hs32232212 : InSquare (37/640) (251/640) (1/640) tau := by
                    convert childUL hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3626.sound htau (by
                    simp only [Batch0453.cell3626, Batch0453.tau3626, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223221 | hy3223221
                · have hs32232211 : InSquare (39/640) (249/640) (1/640) tau := by
                    convert childLR hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3625.sound htau (by
                    simp only [Batch0453.cell3625, Batch0453.tau3625, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232211 (by positivity) using 1 <;> norm_num)
                · have hs32232213 : InSquare (39/640) (251/640) (1/640) tau := by
                    convert childUR hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3627.sound htau (by
                    simp only [Batch0453.cell3627, Batch0453.tau3627, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232213 (by positivity) using 1 <;> norm_num)
            · have hs3223223 : InSquare (19/320) (127/320) (1/320) tau := by
                convert childUR hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223223 | hx3223223
              · rcases le_total tau.im (127/320 : ℝ) with hy3223223 | hy3223223
                · have hs32232230 : InSquare (37/640) (253/640) (1/640) tau := by
                    convert childLL hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact Batch0453.cell3630.sound htau (by
                    simp only [Batch0453.cell3630, Batch0453.tau3630, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232230 (by positivity) using 1 <;> norm_num)
                · have hs32232232 : InSquare (37/640) (51/128) (1/640) tau := by
                    convert childUL hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact (outside_32232232 htau hs32232232).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223223 | hy3223223
                · have hs32232231 : InSquare (39/640) (253/640) (1/640) tau := by
                    convert childLR hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact Batch0453.cell3631.sound htau (by
                    simp only [Batch0453.cell3631, Batch0453.tau3631, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232231 (by positivity) using 1 <;> norm_num)
                · have hs32232233 : InSquare (39/640) (51/128) (1/640) tau := by
                    convert childUR hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact (outside_32232233 htau hs32232233).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32232 | hy32232
        · have hs322321 : InSquare (11/160) (61/160) (1/160) tau := by
            convert childLR hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322321 | hx322321
          · rcases le_total tau.im (61/160 : ℝ) with hy322321 | hy322321
            · have hs3223210 : InSquare (21/320) (121/320) (1/320) tau := by
                convert childLL hs322321 hx322321 hy322321 using 1 <;> norm_num
              exact Batch0288.cell2311.sound htau (by
                simp only [Batch0288.cell2311, Batch0288.tau2311, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223210 (by positivity) using 1 <;> norm_num)
            · have hs3223212 : InSquare (21/320) (123/320) (1/320) tau := by
                convert childUL hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223212 | hx3223212
              · rcases le_total tau.im (123/320 : ℝ) with hy3223212 | hy3223212
                · have hs32232120 : InSquare (41/640) (49/128) (1/640) tau := by
                    convert childLL hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3612.sound htau (by
                    simp only [Batch0451.cell3612, Batch0451.tau3612, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232120 (by positivity) using 1 <;> norm_num)
                · have hs32232122 : InSquare (41/640) (247/640) (1/640) tau := by
                    convert childUL hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3614.sound htau (by
                    simp only [Batch0451.cell3614, Batch0451.tau3614, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223212 | hy3223212
                · have hs32232121 : InSquare (43/640) (49/128) (1/640) tau := by
                    convert childLR hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3613.sound htau (by
                    simp only [Batch0451.cell3613, Batch0451.tau3613, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232121 (by positivity) using 1 <;> norm_num)
                · have hs32232123 : InSquare (43/640) (247/640) (1/640) tau := by
                    convert childUR hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3615.sound htau (by
                    simp only [Batch0451.cell3615, Batch0451.tau3615, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322321 | hy322321
            · have hs3223211 : InSquare (23/320) (121/320) (1/320) tau := by
                convert childLR hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223211 | hx3223211
              · rcases le_total tau.im (121/320 : ℝ) with hy3223211 | hy3223211
                · have hs32232110 : InSquare (9/128) (241/640) (1/640) tau := by
                    convert childLL hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3608.sound htau (by
                    simp only [Batch0451.cell3608, Batch0451.tau3608, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232110 (by positivity) using 1 <;> norm_num)
                · have hs32232112 : InSquare (9/128) (243/640) (1/640) tau := by
                    convert childUL hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3610.sound htau (by
                    simp only [Batch0451.cell3610, Batch0451.tau3610, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223211 | hy3223211
                · have hs32232111 : InSquare (47/640) (241/640) (1/640) tau := by
                    convert childLR hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3609.sound htau (by
                    simp only [Batch0451.cell3609, Batch0451.tau3609, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232111 (by positivity) using 1 <;> norm_num)
                · have hs32232113 : InSquare (47/640) (243/640) (1/640) tau := by
                    convert childUR hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3611.sound htau (by
                    simp only [Batch0451.cell3611, Batch0451.tau3611, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232113 (by positivity) using 1 <;> norm_num)
            · have hs3223213 : InSquare (23/320) (123/320) (1/320) tau := by
                convert childUR hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223213 | hx3223213
              · rcases le_total tau.im (123/320 : ℝ) with hy3223213 | hy3223213
                · have hs32232130 : InSquare (9/128) (49/128) (1/640) tau := by
                    convert childLL hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3616.sound htau (by
                    simp only [Batch0452.cell3616, Batch0452.tau3616, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232130 (by positivity) using 1 <;> norm_num)
                · have hs32232132 : InSquare (9/128) (247/640) (1/640) tau := by
                    convert childUL hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3618.sound htau (by
                    simp only [Batch0452.cell3618, Batch0452.tau3618, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223213 | hy3223213
                · have hs32232131 : InSquare (47/640) (49/128) (1/640) tau := by
                    convert childLR hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3617.sound htau (by
                    simp only [Batch0452.cell3617, Batch0452.tau3617, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232131 (by positivity) using 1 <;> norm_num)
                · have hs32232133 : InSquare (47/640) (247/640) (1/640) tau := by
                    convert childUR hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3619.sound htau (by
                    simp only [Batch0452.cell3619, Batch0452.tau3619, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232133 (by positivity) using 1 <;> norm_num)
        · have hs322323 : InSquare (11/160) (63/160) (1/160) tau := by
            convert childUR hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322323 | hx322323
          · rcases le_total tau.im (63/160 : ℝ) with hy322323 | hy322323
            · have hs3223230 : InSquare (21/320) (25/64) (1/320) tau := by
                convert childLL hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223230 | hx3223230
              · rcases le_total tau.im (25/64 : ℝ) with hy3223230 | hy3223230
                · have hs32232300 : InSquare (41/640) (249/640) (1/640) tau := by
                    convert childLL hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3632.sound htau (by
                    simp only [Batch0454.cell3632, Batch0454.tau3632, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232300 (by positivity) using 1 <;> norm_num)
                · have hs32232302 : InSquare (41/640) (251/640) (1/640) tau := by
                    convert childUL hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3634.sound htau (by
                    simp only [Batch0454.cell3634, Batch0454.tau3634, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223230 | hy3223230
                · have hs32232301 : InSquare (43/640) (249/640) (1/640) tau := by
                    convert childLR hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3633.sound htau (by
                    simp only [Batch0454.cell3633, Batch0454.tau3633, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232301 (by positivity) using 1 <;> norm_num)
                · have hs32232303 : InSquare (43/640) (251/640) (1/640) tau := by
                    convert childUR hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3635.sound htau (by
                    simp only [Batch0454.cell3635, Batch0454.tau3635, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232303 (by positivity) using 1 <;> norm_num)
            · have hs3223232 : InSquare (21/320) (127/320) (1/320) tau := by
                convert childUL hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223232 | hx3223232
              · rcases le_total tau.im (127/320 : ℝ) with hy3223232 | hy3223232
                · have hs32232320 : InSquare (41/640) (253/640) (1/640) tau := by
                    convert childLL hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact Batch0455.cell3640.sound htau (by
                    simp only [Batch0455.cell3640, Batch0455.tau3640, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232320 (by positivity) using 1 <;> norm_num)
                · have hs32232322 : InSquare (41/640) (51/128) (1/640) tau := by
                    convert childUL hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact (outside_32232322 htau hs32232322).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223232 | hy3223232
                · have hs32232321 : InSquare (43/640) (253/640) (1/640) tau := by
                    convert childLR hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact Batch0455.cell3641.sound htau (by
                    simp only [Batch0455.cell3641, Batch0455.tau3641, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232321 (by positivity) using 1 <;> norm_num)
                · have hs32232323 : InSquare (43/640) (51/128) (1/640) tau := by
                    convert childUR hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact (outside_32232323 htau hs32232323).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322323 | hy322323
            · have hs3223231 : InSquare (23/320) (25/64) (1/320) tau := by
                convert childLR hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223231 | hx3223231
              · rcases le_total tau.im (25/64 : ℝ) with hy3223231 | hy3223231
                · have hs32232310 : InSquare (9/128) (249/640) (1/640) tau := by
                    convert childLL hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3636.sound htau (by
                    simp only [Batch0454.cell3636, Batch0454.tau3636, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232310 (by positivity) using 1 <;> norm_num)
                · have hs32232312 : InSquare (9/128) (251/640) (1/640) tau := by
                    convert childUL hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3638.sound htau (by
                    simp only [Batch0454.cell3638, Batch0454.tau3638, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223231 | hy3223231
                · have hs32232311 : InSquare (47/640) (249/640) (1/640) tau := by
                    convert childLR hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3637.sound htau (by
                    simp only [Batch0454.cell3637, Batch0454.tau3637, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232311 (by positivity) using 1 <;> norm_num)
                · have hs32232313 : InSquare (47/640) (251/640) (1/640) tau := by
                    convert childUR hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3639.sound htau (by
                    simp only [Batch0454.cell3639, Batch0454.tau3639, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232313 (by positivity) using 1 <;> norm_num)
            · have hs3223233 : InSquare (23/320) (127/320) (1/320) tau := by
                convert childUR hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223233 | hx3223233
              · rcases le_total tau.im (127/320 : ℝ) with hy3223233 | hy3223233
                · have hs32232330 : InSquare (9/128) (253/640) (1/640) tau := by
                    convert childLL hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact Batch0455.cell3642.sound htau (by
                    simp only [Batch0455.cell3642, Batch0455.tau3642, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232330 (by positivity) using 1 <;> norm_num)
                · have hs32232332 : InSquare (9/128) (51/128) (1/640) tau := by
                    convert childUL hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232332 htau hs32232332).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223233 | hy3223233
                · have hs32232331 : InSquare (47/640) (253/640) (1/640) tau := by
                    convert childLR hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232331 htau hs32232331).elim
                · have hs32232333 : InSquare (47/640) (51/128) (1/640) tau := by
                    convert childUR hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232333 htau hs32232333).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3223 | hy3223
    · have hs32231 : InSquare (7/80) (29/80) (1/80) tau := by
        convert childLR hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32231 | hx32231
      · rcases le_total tau.im (29/80 : ℝ) with hy32231 | hy32231
        · have hs322310 : InSquare (13/160) (57/160) (1/160) tau := by
            convert childLL hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322310 | hx322310
          · rcases le_total tau.im (57/160 : ℝ) with hy322310 | hy322310
            · have hs3223100 : InSquare (5/64) (113/320) (1/320) tau := by
                convert childLL hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2293.sound htau (by
                simp only [Batch0286.cell2293, Batch0286.tau2293, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223100 (by positivity) using 1 <;> norm_num)
            · have hs3223102 : InSquare (5/64) (23/64) (1/320) tau := by
                convert childUL hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2295.sound htau (by
                simp only [Batch0286.cell2295, Batch0286.tau2295, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322310 | hy322310
            · have hs3223101 : InSquare (27/320) (113/320) (1/320) tau := by
                convert childLR hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2294.sound htau (by
                simp only [Batch0286.cell2294, Batch0286.tau2294, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223101 (by positivity) using 1 <;> norm_num)
            · have hs3223103 : InSquare (27/320) (23/64) (1/320) tau := by
                convert childUR hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0287.cell2296.sound htau (by
                simp only [Batch0287.cell2296, Batch0287.tau2296, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223103 (by positivity) using 1 <;> norm_num)
        · have hs322312 : InSquare (13/160) (59/160) (1/160) tau := by
            convert childUL hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322312 | hx322312
          · rcases le_total tau.im (59/160 : ℝ) with hy322312 | hy322312
            · have hs3223120 : InSquare (5/64) (117/320) (1/320) tau := by
                convert childLL hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2301.sound htau (by
                simp only [Batch0287.cell2301, Batch0287.tau2301, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223120 (by positivity) using 1 <;> norm_num)
            · have hs3223122 : InSquare (5/64) (119/320) (1/320) tau := by
                convert childUL hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2303.sound htau (by
                simp only [Batch0287.cell2303, Batch0287.tau2303, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322312 | hy322312
            · have hs3223121 : InSquare (27/320) (117/320) (1/320) tau := by
                convert childLR hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2302.sound htau (by
                simp only [Batch0287.cell2302, Batch0287.tau2302, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223121 (by positivity) using 1 <;> norm_num)
            · have hs3223123 : InSquare (27/320) (119/320) (1/320) tau := by
                convert childUR hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0288.cell2304.sound htau (by
                simp only [Batch0288.cell2304, Batch0288.tau2304, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32231 | hy32231
        · have hs322311 : InSquare (3/32) (57/160) (1/160) tau := by
            convert childLR hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322311 | hx322311
          · rcases le_total tau.im (57/160 : ℝ) with hy322311 | hy322311
            · have hs3223110 : InSquare (29/320) (113/320) (1/320) tau := by
                convert childLL hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2297.sound htau (by
                simp only [Batch0287.cell2297, Batch0287.tau2297, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223110 (by positivity) using 1 <;> norm_num)
            · have hs3223112 : InSquare (29/320) (23/64) (1/320) tau := by
                convert childUL hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2299.sound htau (by
                simp only [Batch0287.cell2299, Batch0287.tau2299, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322311 | hy322311
            · have hs3223111 : InSquare (31/320) (113/320) (1/320) tau := by
                convert childLR hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2298.sound htau (by
                simp only [Batch0287.cell2298, Batch0287.tau2298, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223111 (by positivity) using 1 <;> norm_num)
            · have hs3223113 : InSquare (31/320) (23/64) (1/320) tau := by
                convert childUR hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2300.sound htau (by
                simp only [Batch0287.cell2300, Batch0287.tau2300, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223113 (by positivity) using 1 <;> norm_num)
        · have hs322313 : InSquare (3/32) (59/160) (1/160) tau := by
            convert childUR hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322313 | hx322313
          · rcases le_total tau.im (59/160 : ℝ) with hy322313 | hy322313
            · have hs3223130 : InSquare (29/320) (117/320) (1/320) tau := by
                convert childLL hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2305.sound htau (by
                simp only [Batch0288.cell2305, Batch0288.tau2305, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223130 (by positivity) using 1 <;> norm_num)
            · have hs3223132 : InSquare (29/320) (119/320) (1/320) tau := by
                convert childUL hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2307.sound htau (by
                simp only [Batch0288.cell2307, Batch0288.tau2307, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322313 | hy322313
            · have hs3223131 : InSquare (31/320) (117/320) (1/320) tau := by
                convert childLR hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2306.sound htau (by
                simp only [Batch0288.cell2306, Batch0288.tau2306, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223131 (by positivity) using 1 <;> norm_num)
            · have hs3223133 : InSquare (31/320) (119/320) (1/320) tau := by
                convert childUR hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2308.sound htau (by
                simp only [Batch0288.cell2308, Batch0288.tau2308, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223133 (by positivity) using 1 <;> norm_num)
    · have hs32233 : InSquare (7/80) (31/80) (1/80) tau := by
        convert childUR hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32233 | hx32233
      · rcases le_total tau.im (31/80 : ℝ) with hy32233 | hy32233
        · have hs322330 : InSquare (13/160) (61/160) (1/160) tau := by
            convert childLL hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322330 | hx322330
          · rcases le_total tau.im (61/160 : ℝ) with hy322330 | hy322330
            · have hs3223300 : InSquare (5/64) (121/320) (1/320) tau := by
                convert childLL hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223300 | hx3223300
              · rcases le_total tau.im (121/320 : ℝ) with hy3223300 | hy3223300
                · have hs32233000 : InSquare (49/640) (241/640) (1/640) tau := by
                    convert childLL hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3643.sound htau (by
                    simp only [Batch0455.cell3643, Batch0455.tau3643, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233000 (by positivity) using 1 <;> norm_num)
                · have hs32233002 : InSquare (49/640) (243/640) (1/640) tau := by
                    convert childUL hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3645.sound htau (by
                    simp only [Batch0455.cell3645, Batch0455.tau3645, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223300 | hy3223300
                · have hs32233001 : InSquare (51/640) (241/640) (1/640) tau := by
                    convert childLR hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3644.sound htau (by
                    simp only [Batch0455.cell3644, Batch0455.tau3644, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233001 (by positivity) using 1 <;> norm_num)
                · have hs32233003 : InSquare (51/640) (243/640) (1/640) tau := by
                    convert childUR hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3646.sound htau (by
                    simp only [Batch0455.cell3646, Batch0455.tau3646, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233003 (by positivity) using 1 <;> norm_num)
            · have hs3223302 : InSquare (5/64) (123/320) (1/320) tau := by
                convert childUL hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223302 | hx3223302
              · rcases le_total tau.im (123/320 : ℝ) with hy3223302 | hy3223302
                · have hs32233020 : InSquare (49/640) (49/128) (1/640) tau := by
                    convert childLL hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3651.sound htau (by
                    simp only [Batch0456.cell3651, Batch0456.tau3651, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233020 (by positivity) using 1 <;> norm_num)
                · have hs32233022 : InSquare (49/640) (247/640) (1/640) tau := by
                    convert childUL hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3653.sound htau (by
                    simp only [Batch0456.cell3653, Batch0456.tau3653, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223302 | hy3223302
                · have hs32233021 : InSquare (51/640) (49/128) (1/640) tau := by
                    convert childLR hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3652.sound htau (by
                    simp only [Batch0456.cell3652, Batch0456.tau3652, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233021 (by positivity) using 1 <;> norm_num)
                · have hs32233023 : InSquare (51/640) (247/640) (1/640) tau := by
                    convert childUR hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3654.sound htau (by
                    simp only [Batch0456.cell3654, Batch0456.tau3654, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322330 | hy322330
            · have hs3223301 : InSquare (27/320) (121/320) (1/320) tau := by
                convert childLR hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223301 | hx3223301
              · rcases le_total tau.im (121/320 : ℝ) with hy3223301 | hy3223301
                · have hs32233010 : InSquare (53/640) (241/640) (1/640) tau := by
                    convert childLL hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0455.cell3647.sound htau (by
                    simp only [Batch0455.cell3647, Batch0455.tau3647, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233010 (by positivity) using 1 <;> norm_num)
                · have hs32233012 : InSquare (53/640) (243/640) (1/640) tau := by
                    convert childUL hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3649.sound htau (by
                    simp only [Batch0456.cell3649, Batch0456.tau3649, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223301 | hy3223301
                · have hs32233011 : InSquare (11/128) (241/640) (1/640) tau := by
                    convert childLR hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3648.sound htau (by
                    simp only [Batch0456.cell3648, Batch0456.tau3648, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233011 (by positivity) using 1 <;> norm_num)
                · have hs32233013 : InSquare (11/128) (243/640) (1/640) tau := by
                    convert childUR hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3650.sound htau (by
                    simp only [Batch0456.cell3650, Batch0456.tau3650, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233013 (by positivity) using 1 <;> norm_num)
            · have hs3223303 : InSquare (27/320) (123/320) (1/320) tau := by
                convert childUR hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223303 | hx3223303
              · rcases le_total tau.im (123/320 : ℝ) with hy3223303 | hy3223303
                · have hs32233030 : InSquare (53/640) (49/128) (1/640) tau := by
                    convert childLL hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0456.cell3655.sound htau (by
                    simp only [Batch0456.cell3655, Batch0456.tau3655, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233030 (by positivity) using 1 <;> norm_num)
                · have hs32233032 : InSquare (53/640) (247/640) (1/640) tau := by
                    convert childUL hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3657.sound htau (by
                    simp only [Batch0457.cell3657, Batch0457.tau3657, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223303 | hy3223303
                · have hs32233031 : InSquare (11/128) (49/128) (1/640) tau := by
                    convert childLR hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3656.sound htau (by
                    simp only [Batch0457.cell3656, Batch0457.tau3656, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233031 (by positivity) using 1 <;> norm_num)
                · have hs32233033 : InSquare (11/128) (247/640) (1/640) tau := by
                    convert childUR hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3658.sound htau (by
                    simp only [Batch0457.cell3658, Batch0457.tau3658, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233033 (by positivity) using 1 <;> norm_num)
        · have hs322332 : InSquare (13/160) (63/160) (1/160) tau := by
            convert childUL hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322332 | hx322332
          · rcases le_total tau.im (63/160 : ℝ) with hy322332 | hy322332
            · have hs3223320 : InSquare (5/64) (25/64) (1/320) tau := by
                convert childLL hs322332 hx322332 hy322332 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223320 | hx3223320
              · rcases le_total tau.im (25/64 : ℝ) with hy3223320 | hy3223320
                · have hs32233200 : InSquare (49/640) (249/640) (1/640) tau := by
                    convert childLL hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3675.sound htau (by
                    simp only [Batch0459.cell3675, Batch0459.tau3675, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233200 (by positivity) using 1 <;> norm_num)
                · have hs32233202 : InSquare (49/640) (251/640) (1/640) tau := by
                    convert childUL hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3677.sound htau (by
                    simp only [Batch0459.cell3677, Batch0459.tau3677, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223320 | hy3223320
                · have hs32233201 : InSquare (51/640) (249/640) (1/640) tau := by
                    convert childLR hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3676.sound htau (by
                    simp only [Batch0459.cell3676, Batch0459.tau3676, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233201 (by positivity) using 1 <;> norm_num)
                · have hs32233203 : InSquare (51/640) (251/640) (1/640) tau := by
                    convert childUR hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3678.sound htau (by
                    simp only [Batch0459.cell3678, Batch0459.tau3678, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233203 (by positivity) using 1 <;> norm_num)
            · have hs3223322 : InSquare (5/64) (127/320) (1/320) tau := by
                convert childUL hs322332 hx322332 hy322332 using 1 <;> norm_num
              exact (outside_3223322 htau hs3223322).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322332 | hy322332
            · have hs3223321 : InSquare (27/320) (25/64) (1/320) tau := by
                convert childLR hs322332 hx322332 hy322332 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223321 | hx3223321
              · rcases le_total tau.im (25/64 : ℝ) with hy3223321 | hy3223321
                · have hs32233210 : InSquare (53/640) (249/640) (1/640) tau := by
                    convert childLL hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0459.cell3679.sound htau (by
                    simp only [Batch0459.cell3679, Batch0459.tau3679, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233210 (by positivity) using 1 <;> norm_num)
                · have hs32233212 : InSquare (53/640) (251/640) (1/640) tau := by
                    convert childUL hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3681.sound htau (by
                    simp only [Batch0460.cell3681, Batch0460.tau3681, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223321 | hy3223321
                · have hs32233211 : InSquare (11/128) (249/640) (1/640) tau := by
                    convert childLR hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3680.sound htau (by
                    simp only [Batch0460.cell3680, Batch0460.tau3680, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233211 (by positivity) using 1 <;> norm_num)
                · have hs32233213 : InSquare (11/128) (251/640) (1/640) tau := by
                    convert childUR hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3682.sound htau (by
                    simp only [Batch0460.cell3682, Batch0460.tau3682, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233213 (by positivity) using 1 <;> norm_num)
            · have hs3223323 : InSquare (27/320) (127/320) (1/320) tau := by
                convert childUR hs322332 hx322332 hy322332 using 1 <;> norm_num
              exact (outside_3223323 htau hs3223323).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32233 | hy32233
        · have hs322331 : InSquare (3/32) (61/160) (1/160) tau := by
            convert childLR hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322331 | hx322331
          · rcases le_total tau.im (61/160 : ℝ) with hy322331 | hy322331
            · have hs3223310 : InSquare (29/320) (121/320) (1/320) tau := by
                convert childLL hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223310 | hx3223310
              · rcases le_total tau.im (121/320 : ℝ) with hy3223310 | hy3223310
                · have hs32233100 : InSquare (57/640) (241/640) (1/640) tau := by
                    convert childLL hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3659.sound htau (by
                    simp only [Batch0457.cell3659, Batch0457.tau3659, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233100 (by positivity) using 1 <;> norm_num)
                · have hs32233102 : InSquare (57/640) (243/640) (1/640) tau := by
                    convert childUL hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3661.sound htau (by
                    simp only [Batch0457.cell3661, Batch0457.tau3661, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223310 | hy3223310
                · have hs32233101 : InSquare (59/640) (241/640) (1/640) tau := by
                    convert childLR hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3660.sound htau (by
                    simp only [Batch0457.cell3660, Batch0457.tau3660, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233101 (by positivity) using 1 <;> norm_num)
                · have hs32233103 : InSquare (59/640) (243/640) (1/640) tau := by
                    convert childUR hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3662.sound htau (by
                    simp only [Batch0457.cell3662, Batch0457.tau3662, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233103 (by positivity) using 1 <;> norm_num)
            · have hs3223312 : InSquare (29/320) (123/320) (1/320) tau := by
                convert childUL hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223312 | hx3223312
              · rcases le_total tau.im (123/320 : ℝ) with hy3223312 | hy3223312
                · have hs32233120 : InSquare (57/640) (49/128) (1/640) tau := by
                    convert childLL hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3667.sound htau (by
                    simp only [Batch0458.cell3667, Batch0458.tau3667, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233120 (by positivity) using 1 <;> norm_num)
                · have hs32233122 : InSquare (57/640) (247/640) (1/640) tau := by
                    convert childUL hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3669.sound htau (by
                    simp only [Batch0458.cell3669, Batch0458.tau3669, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223312 | hy3223312
                · have hs32233121 : InSquare (59/640) (49/128) (1/640) tau := by
                    convert childLR hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3668.sound htau (by
                    simp only [Batch0458.cell3668, Batch0458.tau3668, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233121 (by positivity) using 1 <;> norm_num)
                · have hs32233123 : InSquare (59/640) (247/640) (1/640) tau := by
                    convert childUR hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3670.sound htau (by
                    simp only [Batch0458.cell3670, Batch0458.tau3670, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322331 | hy322331
            · have hs3223311 : InSquare (31/320) (121/320) (1/320) tau := by
                convert childLR hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223311 | hx3223311
              · rcases le_total tau.im (121/320 : ℝ) with hy3223311 | hy3223311
                · have hs32233110 : InSquare (61/640) (241/640) (1/640) tau := by
                    convert childLL hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0457.cell3663.sound htau (by
                    simp only [Batch0457.cell3663, Batch0457.tau3663, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233110 (by positivity) using 1 <;> norm_num)
                · have hs32233112 : InSquare (61/640) (243/640) (1/640) tau := by
                    convert childUL hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3665.sound htau (by
                    simp only [Batch0458.cell3665, Batch0458.tau3665, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223311 | hy3223311
                · have hs32233111 : InSquare (63/640) (241/640) (1/640) tau := by
                    convert childLR hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3664.sound htau (by
                    simp only [Batch0458.cell3664, Batch0458.tau3664, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233111 (by positivity) using 1 <;> norm_num)
                · have hs32233113 : InSquare (63/640) (243/640) (1/640) tau := by
                    convert childUR hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3666.sound htau (by
                    simp only [Batch0458.cell3666, Batch0458.tau3666, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233113 (by positivity) using 1 <;> norm_num)
            · have hs3223313 : InSquare (31/320) (123/320) (1/320) tau := by
                convert childUR hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223313 | hx3223313
              · rcases le_total tau.im (123/320 : ℝ) with hy3223313 | hy3223313
                · have hs32233130 : InSquare (61/640) (49/128) (1/640) tau := by
                    convert childLL hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0458.cell3671.sound htau (by
                    simp only [Batch0458.cell3671, Batch0458.tau3671, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233130 (by positivity) using 1 <;> norm_num)
                · have hs32233132 : InSquare (61/640) (247/640) (1/640) tau := by
                    convert childUL hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3673.sound htau (by
                    simp only [Batch0459.cell3673, Batch0459.tau3673, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223313 | hy3223313
                · have hs32233131 : InSquare (63/640) (49/128) (1/640) tau := by
                    convert childLR hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3672.sound htau (by
                    simp only [Batch0459.cell3672, Batch0459.tau3672, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233131 (by positivity) using 1 <;> norm_num)
                · have hs32233133 : InSquare (63/640) (247/640) (1/640) tau := by
                    convert childUR hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3674.sound htau (by
                    simp only [Batch0459.cell3674, Batch0459.tau3674, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233133 (by positivity) using 1 <;> norm_num)
        · have hs322333 : InSquare (3/32) (63/160) (1/160) tau := by
            convert childUR hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322333 | hx322333
          · rcases le_total tau.im (63/160 : ℝ) with hy322333 | hy322333
            · have hs3223330 : InSquare (29/320) (25/64) (1/320) tau := by
                convert childLL hs322333 hx322333 hy322333 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223330 | hx3223330
              · rcases le_total tau.im (25/64 : ℝ) with hy3223330 | hy3223330
                · have hs32233300 : InSquare (57/640) (249/640) (1/640) tau := by
                    convert childLL hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact Batch0460.cell3683.sound htau (by
                    simp only [Batch0460.cell3683, Batch0460.tau3683, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233300 (by positivity) using 1 <;> norm_num)
                · have hs32233302 : InSquare (57/640) (251/640) (1/640) tau := by
                    convert childUL hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact (outside_32233302 htau hs32233302).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy3223330 | hy3223330
                · have hs32233301 : InSquare (59/640) (249/640) (1/640) tau := by
                    convert childLR hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact Batch0460.cell3684.sound htau (by
                    simp only [Batch0460.cell3684, Batch0460.tau3684, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233301 (by positivity) using 1 <;> norm_num)
                · have hs32233303 : InSquare (59/640) (251/640) (1/640) tau := by
                    convert childUR hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact (outside_32233303 htau hs32233303).elim
            · have hs3223332 : InSquare (29/320) (127/320) (1/320) tau := by
                convert childUL hs322333 hx322333 hy322333 using 1 <;> norm_num
              exact (outside_3223332 htau hs3223332).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322333 | hy322333
            · have hs3223331 : InSquare (31/320) (25/64) (1/320) tau := by
                convert childLR hs322333 hx322333 hy322333 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223331 | hx3223331
              · rcases le_total tau.im (25/64 : ℝ) with hy3223331 | hy3223331
                · have hs32233310 : InSquare (61/640) (249/640) (1/640) tau := by
                    convert childLL hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact Batch0460.cell3685.sound htau (by
                    simp only [Batch0460.cell3685, Batch0460.tau3685, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233310 (by positivity) using 1 <;> norm_num)
                · have hs32233312 : InSquare (61/640) (251/640) (1/640) tau := by
                    convert childUL hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact (outside_32233312 htau hs32233312).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy3223331 | hy3223331
                · have hs32233311 : InSquare (63/640) (249/640) (1/640) tau := by
                    convert childLR hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact Batch0460.cell3686.sound htau (by
                    simp only [Batch0460.cell3686, Batch0460.tau3686, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233311 (by positivity) using 1 <;> norm_num)
                · have hs32233313 : InSquare (63/640) (251/640) (1/640) tau := by
                    convert childUR hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact (outside_32233313 htau hs32233313).elim
            · have hs3223333 : InSquare (31/320) (127/320) (1/320) tau := by
                convert childUR hs322333 hx322333 hy322333 using 1 <;> norm_num
              exact (outside_3223333 htau hs3223333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3230 | hx3230
  · rcases le_total tau.im (13/40 : ℝ) with hy3230 | hy3230
    · have hs32300 : InSquare (9/80) (5/16) (1/80) tau := by
        convert childLL hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32300 | hx32300
      · rcases le_total tau.im (5/16 : ℝ) with hy32300 | hy32300
        · have hs323000 : InSquare (17/160) (49/160) (1/160) tau := by
            convert childLL hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1141.sound htau (by
            simp only [Batch0142.cell1141, Batch0142.tau1141, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323000 (by positivity) using 1 <;> norm_num)
        · have hs323002 : InSquare (17/160) (51/160) (1/160) tau := by
            convert childUL hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1143.sound htau (by
            simp only [Batch0142.cell1143, Batch0142.tau1143, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32300 | hy32300
        · have hs323001 : InSquare (19/160) (49/160) (1/160) tau := by
            convert childLR hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1142.sound htau (by
            simp only [Batch0142.cell1142, Batch0142.tau1142, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323001 (by positivity) using 1 <;> norm_num)
        · have hs323003 : InSquare (19/160) (51/160) (1/160) tau := by
            convert childUR hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0143.cell1144.sound htau (by
            simp only [Batch0143.cell1144, Batch0143.tau1144, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323003 (by positivity) using 1 <;> norm_num)
    · have hs32302 : InSquare (9/80) (27/80) (1/80) tau := by
        convert childUL hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32302 | hx32302
      · rcases le_total tau.im (27/80 : ℝ) with hy32302 | hy32302
        · have hs323020 : InSquare (17/160) (53/160) (1/160) tau := by
            convert childLL hs32302 hx32302 hy32302 using 1 <;> norm_num
          exact Batch0143.cell1148.sound htau (by
            simp only [Batch0143.cell1148, Batch0143.tau1148, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323020 (by positivity) using 1 <;> norm_num)
        · have hs323022 : InSquare (17/160) (11/32) (1/160) tau := by
            convert childUL hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323022 | hx323022
          · rcases le_total tau.im (11/32 : ℝ) with hy323022 | hy323022
            · have hs3230220 : InSquare (33/320) (109/320) (1/320) tau := by
                convert childLL hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2320.sound htau (by
                simp only [Batch0290.cell2320, Batch0290.tau2320, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230220 (by positivity) using 1 <;> norm_num)
            · have hs3230222 : InSquare (33/320) (111/320) (1/320) tau := by
                convert childUL hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2322.sound htau (by
                simp only [Batch0290.cell2322, Batch0290.tau2322, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323022 | hy323022
            · have hs3230221 : InSquare (7/64) (109/320) (1/320) tau := by
                convert childLR hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2321.sound htau (by
                simp only [Batch0290.cell2321, Batch0290.tau2321, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230221 (by positivity) using 1 <;> norm_num)
            · have hs3230223 : InSquare (7/64) (111/320) (1/320) tau := by
                convert childUR hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2323.sound htau (by
                simp only [Batch0290.cell2323, Batch0290.tau2323, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32302 | hy32302
        · have hs323021 : InSquare (19/160) (53/160) (1/160) tau := by
            convert childLR hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323021 | hx323021
          · rcases le_total tau.im (53/160 : ℝ) with hy323021 | hy323021
            · have hs3230210 : InSquare (37/320) (21/64) (1/320) tau := by
                convert childLL hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2316.sound htau (by
                simp only [Batch0289.cell2316, Batch0289.tau2316, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230210 (by positivity) using 1 <;> norm_num)
            · have hs3230212 : InSquare (37/320) (107/320) (1/320) tau := by
                convert childUL hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2318.sound htau (by
                simp only [Batch0289.cell2318, Batch0289.tau2318, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323021 | hy323021
            · have hs3230211 : InSquare (39/320) (21/64) (1/320) tau := by
                convert childLR hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2317.sound htau (by
                simp only [Batch0289.cell2317, Batch0289.tau2317, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230211 (by positivity) using 1 <;> norm_num)
            · have hs3230213 : InSquare (39/320) (107/320) (1/320) tau := by
                convert childUR hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2319.sound htau (by
                simp only [Batch0289.cell2319, Batch0289.tau2319, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230213 (by positivity) using 1 <;> norm_num)
        · have hs323023 : InSquare (19/160) (11/32) (1/160) tau := by
            convert childUR hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323023 | hx323023
          · rcases le_total tau.im (11/32 : ℝ) with hy323023 | hy323023
            · have hs3230230 : InSquare (37/320) (109/320) (1/320) tau := by
                convert childLL hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2324.sound htau (by
                simp only [Batch0290.cell2324, Batch0290.tau2324, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230230 (by positivity) using 1 <;> norm_num)
            · have hs3230232 : InSquare (37/320) (111/320) (1/320) tau := by
                convert childUL hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2326.sound htau (by
                simp only [Batch0290.cell2326, Batch0290.tau2326, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323023 | hy323023
            · have hs3230231 : InSquare (39/320) (109/320) (1/320) tau := by
                convert childLR hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2325.sound htau (by
                simp only [Batch0290.cell2325, Batch0290.tau2325, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230231 (by positivity) using 1 <;> norm_num)
            · have hs3230233 : InSquare (39/320) (111/320) (1/320) tau := by
                convert childUR hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2327.sound htau (by
                simp only [Batch0290.cell2327, Batch0290.tau2327, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3230 | hy3230
    · have hs32301 : InSquare (11/80) (5/16) (1/80) tau := by
        convert childLR hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32301 | hx32301
      · rcases le_total tau.im (5/16 : ℝ) with hy32301 | hy32301
        · have hs323010 : InSquare (21/160) (49/160) (1/160) tau := by
            convert childLL hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1145.sound htau (by
            simp only [Batch0143.cell1145, Batch0143.tau1145, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323010 (by positivity) using 1 <;> norm_num)
        · have hs323012 : InSquare (21/160) (51/160) (1/160) tau := by
            convert childUL hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1147.sound htau (by
            simp only [Batch0143.cell1147, Batch0143.tau1147, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32301 | hy32301
        · have hs323011 : InSquare (23/160) (49/160) (1/160) tau := by
            convert childLR hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1146.sound htau (by
            simp only [Batch0143.cell1146, Batch0143.tau1146, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323011 (by positivity) using 1 <;> norm_num)
        · have hs323013 : InSquare (23/160) (51/160) (1/160) tau := by
            convert childUR hs32301 hx32301 hy32301 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323013 | hx323013
          · rcases le_total tau.im (51/160 : ℝ) with hy323013 | hy323013
            · have hs3230130 : InSquare (9/64) (101/320) (1/320) tau := by
                convert childLL hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2312.sound htau (by
                simp only [Batch0289.cell2312, Batch0289.tau2312, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230130 (by positivity) using 1 <;> norm_num)
            · have hs3230132 : InSquare (9/64) (103/320) (1/320) tau := by
                convert childUL hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2314.sound htau (by
                simp only [Batch0289.cell2314, Batch0289.tau2314, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323013 | hy323013
            · have hs3230131 : InSquare (47/320) (101/320) (1/320) tau := by
                convert childLR hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2313.sound htau (by
                simp only [Batch0289.cell2313, Batch0289.tau2313, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230131 (by positivity) using 1 <;> norm_num)
            · have hs3230133 : InSquare (47/320) (103/320) (1/320) tau := by
                convert childUR hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2315.sound htau (by
                simp only [Batch0289.cell2315, Batch0289.tau2315, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230133 (by positivity) using 1 <;> norm_num)
    · have hs32303 : InSquare (11/80) (27/80) (1/80) tau := by
        convert childUR hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32303 | hx32303
      · rcases le_total tau.im (27/80 : ℝ) with hy32303 | hy32303
        · have hs323030 : InSquare (21/160) (53/160) (1/160) tau := by
            convert childLL hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323030 | hx323030
          · rcases le_total tau.im (53/160 : ℝ) with hy323030 | hy323030
            · have hs3230300 : InSquare (41/320) (21/64) (1/320) tau := by
                convert childLL hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2328.sound htau (by
                simp only [Batch0291.cell2328, Batch0291.tau2328, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230300 (by positivity) using 1 <;> norm_num)
            · have hs3230302 : InSquare (41/320) (107/320) (1/320) tau := by
                convert childUL hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2330.sound htau (by
                simp only [Batch0291.cell2330, Batch0291.tau2330, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323030 | hy323030
            · have hs3230301 : InSquare (43/320) (21/64) (1/320) tau := by
                convert childLR hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2329.sound htau (by
                simp only [Batch0291.cell2329, Batch0291.tau2329, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230301 (by positivity) using 1 <;> norm_num)
            · have hs3230303 : InSquare (43/320) (107/320) (1/320) tau := by
                convert childUR hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2331.sound htau (by
                simp only [Batch0291.cell2331, Batch0291.tau2331, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230303 (by positivity) using 1 <;> norm_num)
        · have hs323032 : InSquare (21/160) (11/32) (1/160) tau := by
            convert childUL hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323032 | hx323032
          · rcases le_total tau.im (11/32 : ℝ) with hy323032 | hy323032
            · have hs3230320 : InSquare (41/320) (109/320) (1/320) tau := by
                convert childLL hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2336.sound htau (by
                simp only [Batch0292.cell2336, Batch0292.tau2336, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230320 (by positivity) using 1 <;> norm_num)
            · have hs3230322 : InSquare (41/320) (111/320) (1/320) tau := by
                convert childUL hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2338.sound htau (by
                simp only [Batch0292.cell2338, Batch0292.tau2338, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323032 | hy323032
            · have hs3230321 : InSquare (43/320) (109/320) (1/320) tau := by
                convert childLR hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2337.sound htau (by
                simp only [Batch0292.cell2337, Batch0292.tau2337, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230321 (by positivity) using 1 <;> norm_num)
            · have hs3230323 : InSquare (43/320) (111/320) (1/320) tau := by
                convert childUR hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2339.sound htau (by
                simp only [Batch0292.cell2339, Batch0292.tau2339, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32303 | hy32303
        · have hs323031 : InSquare (23/160) (53/160) (1/160) tau := by
            convert childLR hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323031 | hx323031
          · rcases le_total tau.im (53/160 : ℝ) with hy323031 | hy323031
            · have hs3230310 : InSquare (9/64) (21/64) (1/320) tau := by
                convert childLL hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2332.sound htau (by
                simp only [Batch0291.cell2332, Batch0291.tau2332, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230310 (by positivity) using 1 <;> norm_num)
            · have hs3230312 : InSquare (9/64) (107/320) (1/320) tau := by
                convert childUL hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2334.sound htau (by
                simp only [Batch0291.cell2334, Batch0291.tau2334, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323031 | hy323031
            · have hs3230311 : InSquare (47/320) (21/64) (1/320) tau := by
                convert childLR hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2333.sound htau (by
                simp only [Batch0291.cell2333, Batch0291.tau2333, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230311 (by positivity) using 1 <;> norm_num)
            · have hs3230313 : InSquare (47/320) (107/320) (1/320) tau := by
                convert childUR hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2335.sound htau (by
                simp only [Batch0291.cell2335, Batch0291.tau2335, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230313 (by positivity) using 1 <;> norm_num)
        · have hs323033 : InSquare (23/160) (11/32) (1/160) tau := by
            convert childUR hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323033 | hx323033
          · rcases le_total tau.im (11/32 : ℝ) with hy323033 | hy323033
            · have hs3230330 : InSquare (9/64) (109/320) (1/320) tau := by
                convert childLL hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2340.sound htau (by
                simp only [Batch0292.cell2340, Batch0292.tau2340, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230330 (by positivity) using 1 <;> norm_num)
            · have hs3230332 : InSquare (9/64) (111/320) (1/320) tau := by
                convert childUL hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2342.sound htau (by
                simp only [Batch0292.cell2342, Batch0292.tau2342, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323033 | hy323033
            · have hs3230331 : InSquare (47/320) (109/320) (1/320) tau := by
                convert childLR hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2341.sound htau (by
                simp only [Batch0292.cell2341, Batch0292.tau2341, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230331 (by positivity) using 1 <;> norm_num)
            · have hs3230333 : InSquare (47/320) (111/320) (1/320) tau := by
                convert childUR hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2343.sound htau (by
                simp only [Batch0292.cell2343, Batch0292.tau2343, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3231 | hx3231
  · rcases le_total tau.im (13/40 : ℝ) with hy3231 | hy3231
    · have hs32310 : InSquare (13/80) (5/16) (1/80) tau := by
        convert childLL hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32310 | hx32310
      · rcases le_total tau.im (5/16 : ℝ) with hy32310 | hy32310
        · have hs323100 : InSquare (5/32) (49/160) (1/160) tau := by
            convert childLL hs32310 hx32310 hy32310 using 1 <;> norm_num
          exact Batch0143.cell1149.sound htau (by
            simp only [Batch0143.cell1149, Batch0143.tau1149, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323100 (by positivity) using 1 <;> norm_num)
        · have hs323102 : InSquare (5/32) (51/160) (1/160) tau := by
            convert childUL hs32310 hx32310 hy32310 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323102 | hx323102
          · rcases le_total tau.im (51/160 : ℝ) with hy323102 | hy323102
            · have hs3231020 : InSquare (49/320) (101/320) (1/320) tau := by
                convert childLL hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2344.sound htau (by
                simp only [Batch0293.cell2344, Batch0293.tau2344, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231020 (by positivity) using 1 <;> norm_num)
            · have hs3231022 : InSquare (49/320) (103/320) (1/320) tau := by
                convert childUL hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2346.sound htau (by
                simp only [Batch0293.cell2346, Batch0293.tau2346, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323102 | hy323102
            · have hs3231021 : InSquare (51/320) (101/320) (1/320) tau := by
                convert childLR hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2345.sound htau (by
                simp only [Batch0293.cell2345, Batch0293.tau2345, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231021 (by positivity) using 1 <;> norm_num)
            · have hs3231023 : InSquare (51/320) (103/320) (1/320) tau := by
                convert childUR hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2347.sound htau (by
                simp only [Batch0293.cell2347, Batch0293.tau2347, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32310 | hy32310
        · have hs323101 : InSquare (27/160) (49/160) (1/160) tau := by
            convert childLR hs32310 hx32310 hy32310 using 1 <;> norm_num
          exact Batch0143.cell1150.sound htau (by
            simp only [Batch0143.cell1150, Batch0143.tau1150, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323101 (by positivity) using 1 <;> norm_num)
        · have hs323103 : InSquare (27/160) (51/160) (1/160) tau := by
            convert childUR hs32310 hx32310 hy32310 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323103 | hx323103
          · rcases le_total tau.im (51/160 : ℝ) with hy323103 | hy323103
            · have hs3231030 : InSquare (53/320) (101/320) (1/320) tau := by
                convert childLL hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2348.sound htau (by
                simp only [Batch0293.cell2348, Batch0293.tau2348, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231030 (by positivity) using 1 <;> norm_num)
            · have hs3231032 : InSquare (53/320) (103/320) (1/320) tau := by
                convert childUL hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2350.sound htau (by
                simp only [Batch0293.cell2350, Batch0293.tau2350, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323103 | hy323103
            · have hs3231031 : InSquare (11/64) (101/320) (1/320) tau := by
                convert childLR hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2349.sound htau (by
                simp only [Batch0293.cell2349, Batch0293.tau2349, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231031 (by positivity) using 1 <;> norm_num)
            · have hs3231033 : InSquare (11/64) (103/320) (1/320) tau := by
                convert childUR hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2351.sound htau (by
                simp only [Batch0293.cell2351, Batch0293.tau2351, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231033 (by positivity) using 1 <;> norm_num)
    · have hs32312 : InSquare (13/80) (27/80) (1/80) tau := by
        convert childUL hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32312 | hx32312
      · rcases le_total tau.im (27/80 : ℝ) with hy32312 | hy32312
        · have hs323120 : InSquare (5/32) (53/160) (1/160) tau := by
            convert childLL hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323120 | hx323120
          · rcases le_total tau.im (53/160 : ℝ) with hy323120 | hy323120
            · have hs3231200 : InSquare (49/320) (21/64) (1/320) tau := by
                convert childLL hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2368.sound htau (by
                simp only [Batch0296.cell2368, Batch0296.tau2368, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231200 (by positivity) using 1 <;> norm_num)
            · have hs3231202 : InSquare (49/320) (107/320) (1/320) tau := by
                convert childUL hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2370.sound htau (by
                simp only [Batch0296.cell2370, Batch0296.tau2370, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323120 | hy323120
            · have hs3231201 : InSquare (51/320) (21/64) (1/320) tau := by
                convert childLR hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2369.sound htau (by
                simp only [Batch0296.cell2369, Batch0296.tau2369, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231201 (by positivity) using 1 <;> norm_num)
            · have hs3231203 : InSquare (51/320) (107/320) (1/320) tau := by
                convert childUR hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2371.sound htau (by
                simp only [Batch0296.cell2371, Batch0296.tau2371, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231203 (by positivity) using 1 <;> norm_num)
        · have hs323122 : InSquare (5/32) (11/32) (1/160) tau := by
            convert childUL hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323122 | hx323122
          · rcases le_total tau.im (11/32 : ℝ) with hy323122 | hy323122
            · have hs3231220 : InSquare (49/320) (109/320) (1/320) tau := by
                convert childLL hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2376.sound htau (by
                simp only [Batch0297.cell2376, Batch0297.tau2376, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231220 (by positivity) using 1 <;> norm_num)
            · have hs3231222 : InSquare (49/320) (111/320) (1/320) tau := by
                convert childUL hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2378.sound htau (by
                simp only [Batch0297.cell2378, Batch0297.tau2378, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323122 | hy323122
            · have hs3231221 : InSquare (51/320) (109/320) (1/320) tau := by
                convert childLR hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2377.sound htau (by
                simp only [Batch0297.cell2377, Batch0297.tau2377, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231221 (by positivity) using 1 <;> norm_num)
            · have hs3231223 : InSquare (51/320) (111/320) (1/320) tau := by
                convert childUR hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2379.sound htau (by
                simp only [Batch0297.cell2379, Batch0297.tau2379, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32312 | hy32312
        · have hs323121 : InSquare (27/160) (53/160) (1/160) tau := by
            convert childLR hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323121 | hx323121
          · rcases le_total tau.im (53/160 : ℝ) with hy323121 | hy323121
            · have hs3231210 : InSquare (53/320) (21/64) (1/320) tau := by
                convert childLL hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2372.sound htau (by
                simp only [Batch0296.cell2372, Batch0296.tau2372, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231210 (by positivity) using 1 <;> norm_num)
            · have hs3231212 : InSquare (53/320) (107/320) (1/320) tau := by
                convert childUL hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2374.sound htau (by
                simp only [Batch0296.cell2374, Batch0296.tau2374, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323121 | hy323121
            · have hs3231211 : InSquare (11/64) (21/64) (1/320) tau := by
                convert childLR hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2373.sound htau (by
                simp only [Batch0296.cell2373, Batch0296.tau2373, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231211 (by positivity) using 1 <;> norm_num)
            · have hs3231213 : InSquare (11/64) (107/320) (1/320) tau := by
                convert childUR hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2375.sound htau (by
                simp only [Batch0296.cell2375, Batch0296.tau2375, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231213 (by positivity) using 1 <;> norm_num)
        · have hs323123 : InSquare (27/160) (11/32) (1/160) tau := by
            convert childUR hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323123 | hx323123
          · rcases le_total tau.im (11/32 : ℝ) with hy323123 | hy323123
            · have hs3231230 : InSquare (53/320) (109/320) (1/320) tau := by
                convert childLL hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2380.sound htau (by
                simp only [Batch0297.cell2380, Batch0297.tau2380, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231230 (by positivity) using 1 <;> norm_num)
            · have hs3231232 : InSquare (53/320) (111/320) (1/320) tau := by
                convert childUL hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2382.sound htau (by
                simp only [Batch0297.cell2382, Batch0297.tau2382, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323123 | hy323123
            · have hs3231231 : InSquare (11/64) (109/320) (1/320) tau := by
                convert childLR hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2381.sound htau (by
                simp only [Batch0297.cell2381, Batch0297.tau2381, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231231 (by positivity) using 1 <;> norm_num)
            · have hs3231233 : InSquare (11/64) (111/320) (1/320) tau := by
                convert childUR hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2383.sound htau (by
                simp only [Batch0297.cell2383, Batch0297.tau2383, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3231 | hy3231
    · have hs32311 : InSquare (3/16) (5/16) (1/80) tau := by
        convert childLR hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32311 | hx32311
      · rcases le_total tau.im (5/16 : ℝ) with hy32311 | hy32311
        · have hs323110 : InSquare (29/160) (49/160) (1/160) tau := by
            convert childLL hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323110 | hx323110
          · rcases le_total tau.im (49/160 : ℝ) with hy323110 | hy323110
            · have hs3231100 : InSquare (57/320) (97/320) (1/320) tau := by
                convert childLL hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2352.sound htau (by
                simp only [Batch0294.cell2352, Batch0294.tau2352, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231100 (by positivity) using 1 <;> norm_num)
            · have hs3231102 : InSquare (57/320) (99/320) (1/320) tau := by
                convert childUL hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2354.sound htau (by
                simp only [Batch0294.cell2354, Batch0294.tau2354, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy323110 | hy323110
            · have hs3231101 : InSquare (59/320) (97/320) (1/320) tau := by
                convert childLR hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2353.sound htau (by
                simp only [Batch0294.cell2353, Batch0294.tau2353, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231101 (by positivity) using 1 <;> norm_num)
            · have hs3231103 : InSquare (59/320) (99/320) (1/320) tau := by
                convert childUR hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2355.sound htau (by
                simp only [Batch0294.cell2355, Batch0294.tau2355, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231103 (by positivity) using 1 <;> norm_num)
        · have hs323112 : InSquare (29/160) (51/160) (1/160) tau := by
            convert childUL hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323112 | hx323112
          · rcases le_total tau.im (51/160 : ℝ) with hy323112 | hy323112
            · have hs3231120 : InSquare (57/320) (101/320) (1/320) tau := by
                convert childLL hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2360.sound htau (by
                simp only [Batch0295.cell2360, Batch0295.tau2360, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231120 (by positivity) using 1 <;> norm_num)
            · have hs3231122 : InSquare (57/320) (103/320) (1/320) tau := by
                convert childUL hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2362.sound htau (by
                simp only [Batch0295.cell2362, Batch0295.tau2362, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323112 | hy323112
            · have hs3231121 : InSquare (59/320) (101/320) (1/320) tau := by
                convert childLR hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2361.sound htau (by
                simp only [Batch0295.cell2361, Batch0295.tau2361, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231121 (by positivity) using 1 <;> norm_num)
            · have hs3231123 : InSquare (59/320) (103/320) (1/320) tau := by
                convert childUR hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2363.sound htau (by
                simp only [Batch0295.cell2363, Batch0295.tau2363, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32311 | hy32311
        · have hs323111 : InSquare (31/160) (49/160) (1/160) tau := by
            convert childLR hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323111 | hx323111
          · rcases le_total tau.im (49/160 : ℝ) with hy323111 | hy323111
            · have hs3231110 : InSquare (61/320) (97/320) (1/320) tau := by
                convert childLL hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2356.sound htau (by
                simp only [Batch0294.cell2356, Batch0294.tau2356, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231110 (by positivity) using 1 <;> norm_num)
            · have hs3231112 : InSquare (61/320) (99/320) (1/320) tau := by
                convert childUL hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2358.sound htau (by
                simp only [Batch0294.cell2358, Batch0294.tau2358, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy323111 | hy323111
            · have hs3231111 : InSquare (63/320) (97/320) (1/320) tau := by
                convert childLR hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2357.sound htau (by
                simp only [Batch0294.cell2357, Batch0294.tau2357, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231111 (by positivity) using 1 <;> norm_num)
            · have hs3231113 : InSquare (63/320) (99/320) (1/320) tau := by
                convert childUR hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2359.sound htau (by
                simp only [Batch0294.cell2359, Batch0294.tau2359, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231113 (by positivity) using 1 <;> norm_num)
        · have hs323113 : InSquare (31/160) (51/160) (1/160) tau := by
            convert childUR hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323113 | hx323113
          · rcases le_total tau.im (51/160 : ℝ) with hy323113 | hy323113
            · have hs3231130 : InSquare (61/320) (101/320) (1/320) tau := by
                convert childLL hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2364.sound htau (by
                simp only [Batch0295.cell2364, Batch0295.tau2364, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231130 (by positivity) using 1 <;> norm_num)
            · have hs3231132 : InSquare (61/320) (103/320) (1/320) tau := by
                convert childUL hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2366.sound htau (by
                simp only [Batch0295.cell2366, Batch0295.tau2366, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323113 | hy323113
            · have hs3231131 : InSquare (63/320) (101/320) (1/320) tau := by
                convert childLR hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2365.sound htau (by
                simp only [Batch0295.cell2365, Batch0295.tau2365, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231131 (by positivity) using 1 <;> norm_num)
            · have hs3231133 : InSquare (63/320) (103/320) (1/320) tau := by
                convert childUR hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2367.sound htau (by
                simp only [Batch0295.cell2367, Batch0295.tau2367, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231133 (by positivity) using 1 <;> norm_num)
    · have hs32313 : InSquare (3/16) (27/80) (1/80) tau := by
        convert childUR hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32313 | hx32313
      · rcases le_total tau.im (27/80 : ℝ) with hy32313 | hy32313
        · have hs323130 : InSquare (29/160) (53/160) (1/160) tau := by
            convert childLL hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323130 | hx323130
          · rcases le_total tau.im (53/160 : ℝ) with hy323130 | hy323130
            · have hs3231300 : InSquare (57/320) (21/64) (1/320) tau := by
                convert childLL hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2384.sound htau (by
                simp only [Batch0298.cell2384, Batch0298.tau2384, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231300 (by positivity) using 1 <;> norm_num)
            · have hs3231302 : InSquare (57/320) (107/320) (1/320) tau := by
                convert childUL hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2386.sound htau (by
                simp only [Batch0298.cell2386, Batch0298.tau2386, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323130 | hy323130
            · have hs3231301 : InSquare (59/320) (21/64) (1/320) tau := by
                convert childLR hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2385.sound htau (by
                simp only [Batch0298.cell2385, Batch0298.tau2385, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231301 (by positivity) using 1 <;> norm_num)
            · have hs3231303 : InSquare (59/320) (107/320) (1/320) tau := by
                convert childUR hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2387.sound htau (by
                simp only [Batch0298.cell2387, Batch0298.tau2387, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231303 (by positivity) using 1 <;> norm_num)
        · have hs323132 : InSquare (29/160) (11/32) (1/160) tau := by
            convert childUL hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323132 | hx323132
          · rcases le_total tau.im (11/32 : ℝ) with hy323132 | hy323132
            · have hs3231320 : InSquare (57/320) (109/320) (1/320) tau := by
                convert childLL hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2392.sound htau (by
                simp only [Batch0299.cell2392, Batch0299.tau2392, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231320 (by positivity) using 1 <;> norm_num)
            · have hs3231322 : InSquare (57/320) (111/320) (1/320) tau := by
                convert childUL hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2394.sound htau (by
                simp only [Batch0299.cell2394, Batch0299.tau2394, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323132 | hy323132
            · have hs3231321 : InSquare (59/320) (109/320) (1/320) tau := by
                convert childLR hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2393.sound htau (by
                simp only [Batch0299.cell2393, Batch0299.tau2393, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231321 (by positivity) using 1 <;> norm_num)
            · have hs3231323 : InSquare (59/320) (111/320) (1/320) tau := by
                convert childUR hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2395.sound htau (by
                simp only [Batch0299.cell2395, Batch0299.tau2395, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32313 | hy32313
        · have hs323131 : InSquare (31/160) (53/160) (1/160) tau := by
            convert childLR hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323131 | hx323131
          · rcases le_total tau.im (53/160 : ℝ) with hy323131 | hy323131
            · have hs3231310 : InSquare (61/320) (21/64) (1/320) tau := by
                convert childLL hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2388.sound htau (by
                simp only [Batch0298.cell2388, Batch0298.tau2388, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231310 (by positivity) using 1 <;> norm_num)
            · have hs3231312 : InSquare (61/320) (107/320) (1/320) tau := by
                convert childUL hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2390.sound htau (by
                simp only [Batch0298.cell2390, Batch0298.tau2390, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323131 | hy323131
            · have hs3231311 : InSquare (63/320) (21/64) (1/320) tau := by
                convert childLR hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2389.sound htau (by
                simp only [Batch0298.cell2389, Batch0298.tau2389, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231311 (by positivity) using 1 <;> norm_num)
            · have hs3231313 : InSquare (63/320) (107/320) (1/320) tau := by
                convert childUR hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2391.sound htau (by
                simp only [Batch0298.cell2391, Batch0298.tau2391, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231313 (by positivity) using 1 <;> norm_num)
        · have hs323133 : InSquare (31/160) (11/32) (1/160) tau := by
            convert childUR hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323133 | hx323133
          · rcases le_total tau.im (11/32 : ℝ) with hy323133 | hy323133
            · have hs3231330 : InSquare (61/320) (109/320) (1/320) tau := by
                convert childLL hs323133 hx323133 hy323133 using 1 <;> norm_num
              exact Batch0299.cell2396.sound htau (by
                simp only [Batch0299.cell2396, Batch0299.tau2396, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231330 (by positivity) using 1 <;> norm_num)
            · have hs3231332 : InSquare (61/320) (111/320) (1/320) tau := by
                convert childUL hs323133 hx323133 hy323133 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx3231332 | hx3231332
              · rcases le_total tau.im (111/320 : ℝ) with hy3231332 | hy3231332
                · have hs32313320 : InSquare (121/640) (221/640) (1/640) tau := by
                    convert childLL hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0460.cell3687.sound htau (by
                    simp only [Batch0460.cell3687, Batch0460.tau3687, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313320 (by positivity) using 1 <;> norm_num)
                · have hs32313322 : InSquare (121/640) (223/640) (1/640) tau := by
                    convert childUL hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3689.sound htau (by
                    simp only [Batch0461.cell3689, Batch0461.tau3689, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy3231332 | hy3231332
                · have hs32313321 : InSquare (123/640) (221/640) (1/640) tau := by
                    convert childLR hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3688.sound htau (by
                    simp only [Batch0461.cell3688, Batch0461.tau3688, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313321 (by positivity) using 1 <;> norm_num)
                · have hs32313323 : InSquare (123/640) (223/640) (1/640) tau := by
                    convert childUR hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3690.sound htau (by
                    simp only [Batch0461.cell3690, Batch0461.tau3690, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323133 | hy323133
            · have hs3231331 : InSquare (63/320) (109/320) (1/320) tau := by
                convert childLR hs323133 hx323133 hy323133 using 1 <;> norm_num
              exact Batch0299.cell2397.sound htau (by
                simp only [Batch0299.cell2397, Batch0299.tau2397, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231331 (by positivity) using 1 <;> norm_num)
            · have hs3231333 : InSquare (63/320) (111/320) (1/320) tau := by
                convert childUR hs323133 hx323133 hy323133 using 1 <;> norm_num
              rcases le_total tau.re (63/320 : ℝ) with hx3231333 | hx3231333
              · rcases le_total tau.im (111/320 : ℝ) with hy3231333 | hy3231333
                · have hs32313330 : InSquare (25/128) (221/640) (1/640) tau := by
                    convert childLL hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3691.sound htau (by
                    simp only [Batch0461.cell3691, Batch0461.tau3691, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313330 (by positivity) using 1 <;> norm_num)
                · have hs32313332 : InSquare (25/128) (223/640) (1/640) tau := by
                    convert childUL hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3693.sound htau (by
                    simp only [Batch0461.cell3693, Batch0461.tau3693, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy3231333 | hy3231333
                · have hs32313331 : InSquare (127/640) (221/640) (1/640) tau := by
                    convert childLR hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3692.sound htau (by
                    simp only [Batch0461.cell3692, Batch0461.tau3692, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313331 (by positivity) using 1 <;> norm_num)
                · have hs32313333 : InSquare (127/640) (223/640) (1/640) tau := by
                    convert childUR hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3694.sound htau (by
                    simp only [Batch0461.cell3694, Batch0461.tau3694, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_323222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/64) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/128) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (77/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/128) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3232 | hx3232
  · rcases le_total tau.im (3/8 : ℝ) with hy3232 | hy3232
    · have hs32320 : InSquare (9/80) (29/80) (1/80) tau := by
        convert childLL hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32320 | hx32320
      · rcases le_total tau.im (29/80 : ℝ) with hy32320 | hy32320
        · have hs323200 : InSquare (17/160) (57/160) (1/160) tau := by
            convert childLL hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323200 | hx323200
          · rcases le_total tau.im (57/160 : ℝ) with hy323200 | hy323200
            · have hs3232000 : InSquare (33/320) (113/320) (1/320) tau := by
                convert childLL hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0299.cell2398.sound htau (by
                simp only [Batch0299.cell2398, Batch0299.tau2398, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232000 (by positivity) using 1 <;> norm_num)
            · have hs3232002 : InSquare (33/320) (23/64) (1/320) tau := by
                convert childUL hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0300.cell2400.sound htau (by
                simp only [Batch0300.cell2400, Batch0300.tau2400, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323200 | hy323200
            · have hs3232001 : InSquare (7/64) (113/320) (1/320) tau := by
                convert childLR hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0299.cell2399.sound htau (by
                simp only [Batch0299.cell2399, Batch0299.tau2399, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232001 (by positivity) using 1 <;> norm_num)
            · have hs3232003 : InSquare (7/64) (23/64) (1/320) tau := by
                convert childUR hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0300.cell2401.sound htau (by
                simp only [Batch0300.cell2401, Batch0300.tau2401, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232003 (by positivity) using 1 <;> norm_num)
        · have hs323202 : InSquare (17/160) (59/160) (1/160) tau := by
            convert childUL hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323202 | hx323202
          · rcases le_total tau.im (59/160 : ℝ) with hy323202 | hy323202
            · have hs3232020 : InSquare (33/320) (117/320) (1/320) tau := by
                convert childLL hs323202 hx323202 hy323202 using 1 <;> norm_num
              exact Batch0300.cell2406.sound htau (by
                simp only [Batch0300.cell2406, Batch0300.tau2406, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232020 (by positivity) using 1 <;> norm_num)
            · have hs3232022 : InSquare (33/320) (119/320) (1/320) tau := by
                convert childUL hs323202 hx323202 hy323202 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232022 | hx3232022
              · rcases le_total tau.im (119/320 : ℝ) with hy3232022 | hy3232022
                · have hs32320220 : InSquare (13/128) (237/640) (1/640) tau := by
                    convert childLL hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0461.cell3695.sound htau (by
                    simp only [Batch0461.cell3695, Batch0461.tau3695, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320220 (by positivity) using 1 <;> norm_num)
                · have hs32320222 : InSquare (13/128) (239/640) (1/640) tau := by
                    convert childUL hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3697.sound htau (by
                    simp only [Batch0462.cell3697, Batch0462.tau3697, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232022 | hy3232022
                · have hs32320221 : InSquare (67/640) (237/640) (1/640) tau := by
                    convert childLR hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3696.sound htau (by
                    simp only [Batch0462.cell3696, Batch0462.tau3696, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320221 (by positivity) using 1 <;> norm_num)
                · have hs32320223 : InSquare (67/640) (239/640) (1/640) tau := by
                    convert childUR hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3698.sound htau (by
                    simp only [Batch0462.cell3698, Batch0462.tau3698, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323202 | hy323202
            · have hs3232021 : InSquare (7/64) (117/320) (1/320) tau := by
                convert childLR hs323202 hx323202 hy323202 using 1 <;> norm_num
              exact Batch0300.cell2407.sound htau (by
                simp only [Batch0300.cell2407, Batch0300.tau2407, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232021 (by positivity) using 1 <;> norm_num)
            · have hs3232023 : InSquare (7/64) (119/320) (1/320) tau := by
                convert childUR hs323202 hx323202 hy323202 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232023 | hx3232023
              · rcases le_total tau.im (119/320 : ℝ) with hy3232023 | hy3232023
                · have hs32320230 : InSquare (69/640) (237/640) (1/640) tau := by
                    convert childLL hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3699.sound htau (by
                    simp only [Batch0462.cell3699, Batch0462.tau3699, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320230 (by positivity) using 1 <;> norm_num)
                · have hs32320232 : InSquare (69/640) (239/640) (1/640) tau := by
                    convert childUL hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3701.sound htau (by
                    simp only [Batch0462.cell3701, Batch0462.tau3701, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232023 | hy3232023
                · have hs32320231 : InSquare (71/640) (237/640) (1/640) tau := by
                    convert childLR hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3700.sound htau (by
                    simp only [Batch0462.cell3700, Batch0462.tau3700, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320231 (by positivity) using 1 <;> norm_num)
                · have hs32320233 : InSquare (71/640) (239/640) (1/640) tau := by
                    convert childUR hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3702.sound htau (by
                    simp only [Batch0462.cell3702, Batch0462.tau3702, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32320 | hy32320
        · have hs323201 : InSquare (19/160) (57/160) (1/160) tau := by
            convert childLR hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323201 | hx323201
          · rcases le_total tau.im (57/160 : ℝ) with hy323201 | hy323201
            · have hs3232010 : InSquare (37/320) (113/320) (1/320) tau := by
                convert childLL hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2402.sound htau (by
                simp only [Batch0300.cell2402, Batch0300.tau2402, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232010 (by positivity) using 1 <;> norm_num)
            · have hs3232012 : InSquare (37/320) (23/64) (1/320) tau := by
                convert childUL hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2404.sound htau (by
                simp only [Batch0300.cell2404, Batch0300.tau2404, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323201 | hy323201
            · have hs3232011 : InSquare (39/320) (113/320) (1/320) tau := by
                convert childLR hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2403.sound htau (by
                simp only [Batch0300.cell2403, Batch0300.tau2403, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232011 (by positivity) using 1 <;> norm_num)
            · have hs3232013 : InSquare (39/320) (23/64) (1/320) tau := by
                convert childUR hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2405.sound htau (by
                simp only [Batch0300.cell2405, Batch0300.tau2405, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232013 (by positivity) using 1 <;> norm_num)
        · have hs323203 : InSquare (19/160) (59/160) (1/160) tau := by
            convert childUR hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323203 | hx323203
          · rcases le_total tau.im (59/160 : ℝ) with hy323203 | hy323203
            · have hs3232030 : InSquare (37/320) (117/320) (1/320) tau := by
                convert childLL hs323203 hx323203 hy323203 using 1 <;> norm_num
              exact Batch0301.cell2408.sound htau (by
                simp only [Batch0301.cell2408, Batch0301.tau2408, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232030 (by positivity) using 1 <;> norm_num)
            · have hs3232032 : InSquare (37/320) (119/320) (1/320) tau := by
                convert childUL hs323203 hx323203 hy323203 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232032 | hx3232032
              · rcases le_total tau.im (119/320 : ℝ) with hy3232032 | hy3232032
                · have hs32320320 : InSquare (73/640) (237/640) (1/640) tau := by
                    convert childLL hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0462.cell3703.sound htau (by
                    simp only [Batch0462.cell3703, Batch0462.tau3703, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320320 (by positivity) using 1 <;> norm_num)
                · have hs32320322 : InSquare (73/640) (239/640) (1/640) tau := by
                    convert childUL hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3705.sound htau (by
                    simp only [Batch0463.cell3705, Batch0463.tau3705, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232032 | hy3232032
                · have hs32320321 : InSquare (15/128) (237/640) (1/640) tau := by
                    convert childLR hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3704.sound htau (by
                    simp only [Batch0463.cell3704, Batch0463.tau3704, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320321 (by positivity) using 1 <;> norm_num)
                · have hs32320323 : InSquare (15/128) (239/640) (1/640) tau := by
                    convert childUR hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3706.sound htau (by
                    simp only [Batch0463.cell3706, Batch0463.tau3706, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323203 | hy323203
            · have hs3232031 : InSquare (39/320) (117/320) (1/320) tau := by
                convert childLR hs323203 hx323203 hy323203 using 1 <;> norm_num
              exact Batch0301.cell2409.sound htau (by
                simp only [Batch0301.cell2409, Batch0301.tau2409, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232031 (by positivity) using 1 <;> norm_num)
            · have hs3232033 : InSquare (39/320) (119/320) (1/320) tau := by
                convert childUR hs323203 hx323203 hy323203 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232033 | hx3232033
              · rcases le_total tau.im (119/320 : ℝ) with hy3232033 | hy3232033
                · have hs32320330 : InSquare (77/640) (237/640) (1/640) tau := by
                    convert childLL hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3707.sound htau (by
                    simp only [Batch0463.cell3707, Batch0463.tau3707, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320330 (by positivity) using 1 <;> norm_num)
                · have hs32320332 : InSquare (77/640) (239/640) (1/640) tau := by
                    convert childUL hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3709.sound htau (by
                    simp only [Batch0463.cell3709, Batch0463.tau3709, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232033 | hy3232033
                · have hs32320331 : InSquare (79/640) (237/640) (1/640) tau := by
                    convert childLR hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3708.sound htau (by
                    simp only [Batch0463.cell3708, Batch0463.tau3708, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320331 (by positivity) using 1 <;> norm_num)
                · have hs32320333 : InSquare (79/640) (239/640) (1/640) tau := by
                    convert childUR hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3710.sound htau (by
                    simp only [Batch0463.cell3710, Batch0463.tau3710, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320333 (by positivity) using 1 <;> norm_num)
    · have hs32322 : InSquare (9/80) (31/80) (1/80) tau := by
        convert childUL hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32322 | hx32322
      · rcases le_total tau.im (31/80 : ℝ) with hy32322 | hy32322
        · have hs323220 : InSquare (17/160) (61/160) (1/160) tau := by
            convert childLL hs32322 hx32322 hy32322 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323220 | hx323220
          · rcases le_total tau.im (61/160 : ℝ) with hy323220 | hy323220
            · have hs3232200 : InSquare (33/320) (121/320) (1/320) tau := by
                convert childLL hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232200 | hx3232200
              · rcases le_total tau.im (121/320 : ℝ) with hy3232200 | hy3232200
                · have hs32322000 : InSquare (13/128) (241/640) (1/640) tau := by
                    convert childLL hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3747.sound htau (by
                    simp only [Batch0468.cell3747, Batch0468.tau3747, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322000 (by positivity) using 1 <;> norm_num)
                · have hs32322002 : InSquare (13/128) (243/640) (1/640) tau := by
                    convert childUL hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3749.sound htau (by
                    simp only [Batch0468.cell3749, Batch0468.tau3749, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232200 | hy3232200
                · have hs32322001 : InSquare (67/640) (241/640) (1/640) tau := by
                    convert childLR hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3748.sound htau (by
                    simp only [Batch0468.cell3748, Batch0468.tau3748, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322001 (by positivity) using 1 <;> norm_num)
                · have hs32322003 : InSquare (67/640) (243/640) (1/640) tau := by
                    convert childUR hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3750.sound htau (by
                    simp only [Batch0468.cell3750, Batch0468.tau3750, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322003 (by positivity) using 1 <;> norm_num)
            · have hs3232202 : InSquare (33/320) (123/320) (1/320) tau := by
                convert childUL hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232202 | hx3232202
              · rcases le_total tau.im (123/320 : ℝ) with hy3232202 | hy3232202
                · have hs32322020 : InSquare (13/128) (49/128) (1/640) tau := by
                    convert childLL hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3755.sound htau (by
                    simp only [Batch0469.cell3755, Batch0469.tau3755, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322020 (by positivity) using 1 <;> norm_num)
                · have hs32322022 : InSquare (13/128) (247/640) (1/640) tau := by
                    convert childUL hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3757.sound htau (by
                    simp only [Batch0469.cell3757, Batch0469.tau3757, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3232202 | hy3232202
                · have hs32322021 : InSquare (67/640) (49/128) (1/640) tau := by
                    convert childLR hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3756.sound htau (by
                    simp only [Batch0469.cell3756, Batch0469.tau3756, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322021 (by positivity) using 1 <;> norm_num)
                · have hs32322023 : InSquare (67/640) (247/640) (1/640) tau := by
                    convert childUR hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3758.sound htau (by
                    simp only [Batch0469.cell3758, Batch0469.tau3758, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy323220 | hy323220
            · have hs3232201 : InSquare (7/64) (121/320) (1/320) tau := by
                convert childLR hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232201 | hx3232201
              · rcases le_total tau.im (121/320 : ℝ) with hy3232201 | hy3232201
                · have hs32322010 : InSquare (69/640) (241/640) (1/640) tau := by
                    convert childLL hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0468.cell3751.sound htau (by
                    simp only [Batch0468.cell3751, Batch0468.tau3751, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322010 (by positivity) using 1 <;> norm_num)
                · have hs32322012 : InSquare (69/640) (243/640) (1/640) tau := by
                    convert childUL hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3753.sound htau (by
                    simp only [Batch0469.cell3753, Batch0469.tau3753, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232201 | hy3232201
                · have hs32322011 : InSquare (71/640) (241/640) (1/640) tau := by
                    convert childLR hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3752.sound htau (by
                    simp only [Batch0469.cell3752, Batch0469.tau3752, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322011 (by positivity) using 1 <;> norm_num)
                · have hs32322013 : InSquare (71/640) (243/640) (1/640) tau := by
                    convert childUR hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3754.sound htau (by
                    simp only [Batch0469.cell3754, Batch0469.tau3754, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322013 (by positivity) using 1 <;> norm_num)
            · have hs3232203 : InSquare (7/64) (123/320) (1/320) tau := by
                convert childUR hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232203 | hx3232203
              · rcases le_total tau.im (123/320 : ℝ) with hy3232203 | hy3232203
                · have hs32322030 : InSquare (69/640) (49/128) (1/640) tau := by
                    convert childLL hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0469.cell3759.sound htau (by
                    simp only [Batch0469.cell3759, Batch0469.tau3759, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322030 (by positivity) using 1 <;> norm_num)
                · have hs32322032 : InSquare (69/640) (247/640) (1/640) tau := by
                    convert childUL hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3761.sound htau (by
                    simp only [Batch0470.cell3761, Batch0470.tau3761, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3232203 | hy3232203
                · have hs32322031 : InSquare (71/640) (49/128) (1/640) tau := by
                    convert childLR hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3760.sound htau (by
                    simp only [Batch0470.cell3760, Batch0470.tau3760, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322031 (by positivity) using 1 <;> norm_num)
                · have hs32322033 : InSquare (71/640) (247/640) (1/640) tau := by
                    convert childUR hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3762.sound htau (by
                    simp only [Batch0470.cell3762, Batch0470.tau3762, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322033 (by positivity) using 1 <;> norm_num)
        · have hs323222 : InSquare (17/160) (63/160) (1/160) tau := by
            convert childUL hs32322 hx32322 hy32322 using 1 <;> norm_num
          exact (outside_323222 htau hs323222).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32322 | hy32322
        · have hs323221 : InSquare (19/160) (61/160) (1/160) tau := by
            convert childLR hs32322 hx32322 hy32322 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323221 | hx323221
          · rcases le_total tau.im (61/160 : ℝ) with hy323221 | hy323221
            · have hs3232210 : InSquare (37/320) (121/320) (1/320) tau := by
                convert childLL hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232210 | hx3232210
              · rcases le_total tau.im (121/320 : ℝ) with hy3232210 | hy3232210
                · have hs32322100 : InSquare (73/640) (241/640) (1/640) tau := by
                    convert childLL hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3763.sound htau (by
                    simp only [Batch0470.cell3763, Batch0470.tau3763, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322100 (by positivity) using 1 <;> norm_num)
                · have hs32322102 : InSquare (73/640) (243/640) (1/640) tau := by
                    convert childUL hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3765.sound htau (by
                    simp only [Batch0470.cell3765, Batch0470.tau3765, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232210 | hy3232210
                · have hs32322101 : InSquare (15/128) (241/640) (1/640) tau := by
                    convert childLR hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3764.sound htau (by
                    simp only [Batch0470.cell3764, Batch0470.tau3764, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322101 (by positivity) using 1 <;> norm_num)
                · have hs32322103 : InSquare (15/128) (243/640) (1/640) tau := by
                    convert childUR hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3766.sound htau (by
                    simp only [Batch0470.cell3766, Batch0470.tau3766, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322103 (by positivity) using 1 <;> norm_num)
            · have hs3232212 : InSquare (37/320) (123/320) (1/320) tau := by
                convert childUL hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232212 | hx3232212
              · rcases le_total tau.im (123/320 : ℝ) with hy3232212 | hy3232212
                · have hs32322120 : InSquare (73/640) (49/128) (1/640) tau := by
                    convert childLL hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact Batch0471.cell3771.sound htau (by
                    simp only [Batch0471.cell3771, Batch0471.tau3771, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322120 (by positivity) using 1 <;> norm_num)
                · have hs32322122 : InSquare (73/640) (247/640) (1/640) tau := by
                    convert childUL hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact (outside_32322122 htau hs32322122).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy3232212 | hy3232212
                · have hs32322121 : InSquare (15/128) (49/128) (1/640) tau := by
                    convert childLR hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact Batch0471.cell3772.sound htau (by
                    simp only [Batch0471.cell3772, Batch0471.tau3772, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322121 (by positivity) using 1 <;> norm_num)
                · have hs32322123 : InSquare (15/128) (247/640) (1/640) tau := by
                    convert childUR hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact (outside_32322123 htau hs32322123).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323221 | hy323221
            · have hs3232211 : InSquare (39/320) (121/320) (1/320) tau := by
                convert childLR hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232211 | hx3232211
              · rcases le_total tau.im (121/320 : ℝ) with hy3232211 | hy3232211
                · have hs32322110 : InSquare (77/640) (241/640) (1/640) tau := by
                    convert childLL hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0470.cell3767.sound htau (by
                    simp only [Batch0470.cell3767, Batch0470.tau3767, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322110 (by positivity) using 1 <;> norm_num)
                · have hs32322112 : InSquare (77/640) (243/640) (1/640) tau := by
                    convert childUL hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3769.sound htau (by
                    simp only [Batch0471.cell3769, Batch0471.tau3769, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232211 | hy3232211
                · have hs32322111 : InSquare (79/640) (241/640) (1/640) tau := by
                    convert childLR hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3768.sound htau (by
                    simp only [Batch0471.cell3768, Batch0471.tau3768, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322111 (by positivity) using 1 <;> norm_num)
                · have hs32322113 : InSquare (79/640) (243/640) (1/640) tau := by
                    convert childUR hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3770.sound htau (by
                    simp only [Batch0471.cell3770, Batch0471.tau3770, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322113 (by positivity) using 1 <;> norm_num)
            · have hs3232213 : InSquare (39/320) (123/320) (1/320) tau := by
                convert childUR hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232213 | hx3232213
              · rcases le_total tau.im (123/320 : ℝ) with hy3232213 | hy3232213
                · have hs32322130 : InSquare (77/640) (49/128) (1/640) tau := by
                    convert childLL hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact Batch0471.cell3773.sound htau (by
                    simp only [Batch0471.cell3773, Batch0471.tau3773, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322130 (by positivity) using 1 <;> norm_num)
                · have hs32322132 : InSquare (77/640) (247/640) (1/640) tau := by
                    convert childUL hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322132 htau hs32322132).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy3232213 | hy3232213
                · have hs32322131 : InSquare (79/640) (49/128) (1/640) tau := by
                    convert childLR hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322131 htau hs32322131).elim
                · have hs32322133 : InSquare (79/640) (247/640) (1/640) tau := by
                    convert childUR hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322133 htau hs32322133).elim
        · have hs323223 : InSquare (19/160) (63/160) (1/160) tau := by
            convert childUR hs32322 hx32322 hy32322 using 1 <;> norm_num
          exact (outside_323223 htau hs323223).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3232 | hy3232
    · have hs32321 : InSquare (11/80) (29/80) (1/80) tau := by
        convert childLR hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32321 | hx32321
      · rcases le_total tau.im (29/80 : ℝ) with hy32321 | hy32321
        · have hs323210 : InSquare (21/160) (57/160) (1/160) tau := by
            convert childLL hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323210 | hx323210
          · rcases le_total tau.im (57/160 : ℝ) with hy323210 | hy323210
            · have hs3232100 : InSquare (41/320) (113/320) (1/320) tau := by
                convert childLL hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2410.sound htau (by
                simp only [Batch0301.cell2410, Batch0301.tau2410, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232100 (by positivity) using 1 <;> norm_num)
            · have hs3232102 : InSquare (41/320) (23/64) (1/320) tau := by
                convert childUL hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2412.sound htau (by
                simp only [Batch0301.cell2412, Batch0301.tau2412, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323210 | hy323210
            · have hs3232101 : InSquare (43/320) (113/320) (1/320) tau := by
                convert childLR hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2411.sound htau (by
                simp only [Batch0301.cell2411, Batch0301.tau2411, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232101 (by positivity) using 1 <;> norm_num)
            · have hs3232103 : InSquare (43/320) (23/64) (1/320) tau := by
                convert childUR hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2413.sound htau (by
                simp only [Batch0301.cell2413, Batch0301.tau2413, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232103 (by positivity) using 1 <;> norm_num)
        · have hs323212 : InSquare (21/160) (59/160) (1/160) tau := by
            convert childUL hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323212 | hx323212
          · rcases le_total tau.im (59/160 : ℝ) with hy323212 | hy323212
            · have hs3232120 : InSquare (41/320) (117/320) (1/320) tau := by
                convert childLL hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232120 | hx3232120
              · rcases le_total tau.im (117/320 : ℝ) with hy3232120 | hy3232120
                · have hs32321200 : InSquare (81/640) (233/640) (1/640) tau := by
                    convert childLL hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3715.sound htau (by
                    simp only [Batch0464.cell3715, Batch0464.tau3715, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321200 (by positivity) using 1 <;> norm_num)
                · have hs32321202 : InSquare (81/640) (47/128) (1/640) tau := by
                    convert childUL hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3717.sound htau (by
                    simp only [Batch0464.cell3717, Batch0464.tau3717, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232120 | hy3232120
                · have hs32321201 : InSquare (83/640) (233/640) (1/640) tau := by
                    convert childLR hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3716.sound htau (by
                    simp only [Batch0464.cell3716, Batch0464.tau3716, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321201 (by positivity) using 1 <;> norm_num)
                · have hs32321203 : InSquare (83/640) (47/128) (1/640) tau := by
                    convert childUR hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3718.sound htau (by
                    simp only [Batch0464.cell3718, Batch0464.tau3718, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321203 (by positivity) using 1 <;> norm_num)
            · have hs3232122 : InSquare (41/320) (119/320) (1/320) tau := by
                convert childUL hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232122 | hx3232122
              · rcases le_total tau.im (119/320 : ℝ) with hy3232122 | hy3232122
                · have hs32321220 : InSquare (81/640) (237/640) (1/640) tau := by
                    convert childLL hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3723.sound htau (by
                    simp only [Batch0465.cell3723, Batch0465.tau3723, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321220 (by positivity) using 1 <;> norm_num)
                · have hs32321222 : InSquare (81/640) (239/640) (1/640) tau := by
                    convert childUL hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3725.sound htau (by
                    simp only [Batch0465.cell3725, Batch0465.tau3725, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232122 | hy3232122
                · have hs32321221 : InSquare (83/640) (237/640) (1/640) tau := by
                    convert childLR hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3724.sound htau (by
                    simp only [Batch0465.cell3724, Batch0465.tau3724, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321221 (by positivity) using 1 <;> norm_num)
                · have hs32321223 : InSquare (83/640) (239/640) (1/640) tau := by
                    convert childUR hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3726.sound htau (by
                    simp only [Batch0465.cell3726, Batch0465.tau3726, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323212 | hy323212
            · have hs3232121 : InSquare (43/320) (117/320) (1/320) tau := by
                convert childLR hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232121 | hx3232121
              · rcases le_total tau.im (117/320 : ℝ) with hy3232121 | hy3232121
                · have hs32321210 : InSquare (17/128) (233/640) (1/640) tau := by
                    convert childLL hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0464.cell3719.sound htau (by
                    simp only [Batch0464.cell3719, Batch0464.tau3719, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321210 (by positivity) using 1 <;> norm_num)
                · have hs32321212 : InSquare (17/128) (47/128) (1/640) tau := by
                    convert childUL hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3721.sound htau (by
                    simp only [Batch0465.cell3721, Batch0465.tau3721, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232121 | hy3232121
                · have hs32321211 : InSquare (87/640) (233/640) (1/640) tau := by
                    convert childLR hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3720.sound htau (by
                    simp only [Batch0465.cell3720, Batch0465.tau3720, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321211 (by positivity) using 1 <;> norm_num)
                · have hs32321213 : InSquare (87/640) (47/128) (1/640) tau := by
                    convert childUR hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3722.sound htau (by
                    simp only [Batch0465.cell3722, Batch0465.tau3722, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321213 (by positivity) using 1 <;> norm_num)
            · have hs3232123 : InSquare (43/320) (119/320) (1/320) tau := by
                convert childUR hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232123 | hx3232123
              · rcases le_total tau.im (119/320 : ℝ) with hy3232123 | hy3232123
                · have hs32321230 : InSquare (17/128) (237/640) (1/640) tau := by
                    convert childLL hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0465.cell3727.sound htau (by
                    simp only [Batch0465.cell3727, Batch0465.tau3727, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321230 (by positivity) using 1 <;> norm_num)
                · have hs32321232 : InSquare (17/128) (239/640) (1/640) tau := by
                    convert childUL hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3729.sound htau (by
                    simp only [Batch0466.cell3729, Batch0466.tau3729, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232123 | hy3232123
                · have hs32321231 : InSquare (87/640) (237/640) (1/640) tau := by
                    convert childLR hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3728.sound htau (by
                    simp only [Batch0466.cell3728, Batch0466.tau3728, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321231 (by positivity) using 1 <;> norm_num)
                · have hs32321233 : InSquare (87/640) (239/640) (1/640) tau := by
                    convert childUR hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3730.sound htau (by
                    simp only [Batch0466.cell3730, Batch0466.tau3730, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32321 | hy32321
        · have hs323211 : InSquare (23/160) (57/160) (1/160) tau := by
            convert childLR hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323211 | hx323211
          · rcases le_total tau.im (57/160 : ℝ) with hy323211 | hy323211
            · have hs3232110 : InSquare (9/64) (113/320) (1/320) tau := by
                convert childLL hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0301.cell2414.sound htau (by
                simp only [Batch0301.cell2414, Batch0301.tau2414, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232110 (by positivity) using 1 <;> norm_num)
            · have hs3232112 : InSquare (9/64) (23/64) (1/320) tau := by
                convert childUL hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0302.cell2416.sound htau (by
                simp only [Batch0302.cell2416, Batch0302.tau2416, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323211 | hy323211
            · have hs3232111 : InSquare (47/320) (113/320) (1/320) tau := by
                convert childLR hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0301.cell2415.sound htau (by
                simp only [Batch0301.cell2415, Batch0301.tau2415, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232111 (by positivity) using 1 <;> norm_num)
            · have hs3232113 : InSquare (47/320) (23/64) (1/320) tau := by
                convert childUR hs323211 hx323211 hy323211 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232113 | hx3232113
              · rcases le_total tau.im (23/64 : ℝ) with hy3232113 | hy3232113
                · have hs32321130 : InSquare (93/640) (229/640) (1/640) tau := by
                    convert childLL hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0463.cell3711.sound htau (by
                    simp only [Batch0463.cell3711, Batch0463.tau3711, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321130 (by positivity) using 1 <;> norm_num)
                · have hs32321132 : InSquare (93/640) (231/640) (1/640) tau := by
                    convert childUL hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3713.sound htau (by
                    simp only [Batch0464.cell3713, Batch0464.tau3713, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3232113 | hy3232113
                · have hs32321131 : InSquare (19/128) (229/640) (1/640) tau := by
                    convert childLR hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3712.sound htau (by
                    simp only [Batch0464.cell3712, Batch0464.tau3712, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321131 (by positivity) using 1 <;> norm_num)
                · have hs32321133 : InSquare (19/128) (231/640) (1/640) tau := by
                    convert childUR hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3714.sound htau (by
                    simp only [Batch0464.cell3714, Batch0464.tau3714, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321133 (by positivity) using 1 <;> norm_num)
        · have hs323213 : InSquare (23/160) (59/160) (1/160) tau := by
            convert childUR hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323213 | hx323213
          · rcases le_total tau.im (59/160 : ℝ) with hy323213 | hy323213
            · have hs3232130 : InSquare (9/64) (117/320) (1/320) tau := by
                convert childLL hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232130 | hx3232130
              · rcases le_total tau.im (117/320 : ℝ) with hy3232130 | hy3232130
                · have hs32321300 : InSquare (89/640) (233/640) (1/640) tau := by
                    convert childLL hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3731.sound htau (by
                    simp only [Batch0466.cell3731, Batch0466.tau3731, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321300 (by positivity) using 1 <;> norm_num)
                · have hs32321302 : InSquare (89/640) (47/128) (1/640) tau := by
                    convert childUL hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3733.sound htau (by
                    simp only [Batch0466.cell3733, Batch0466.tau3733, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232130 | hy3232130
                · have hs32321301 : InSquare (91/640) (233/640) (1/640) tau := by
                    convert childLR hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3732.sound htau (by
                    simp only [Batch0466.cell3732, Batch0466.tau3732, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321301 (by positivity) using 1 <;> norm_num)
                · have hs32321303 : InSquare (91/640) (47/128) (1/640) tau := by
                    convert childUR hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3734.sound htau (by
                    simp only [Batch0466.cell3734, Batch0466.tau3734, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321303 (by positivity) using 1 <;> norm_num)
            · have hs3232132 : InSquare (9/64) (119/320) (1/320) tau := by
                convert childUL hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232132 | hx3232132
              · rcases le_total tau.im (119/320 : ℝ) with hy3232132 | hy3232132
                · have hs32321320 : InSquare (89/640) (237/640) (1/640) tau := by
                    convert childLL hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3739.sound htau (by
                    simp only [Batch0467.cell3739, Batch0467.tau3739, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321320 (by positivity) using 1 <;> norm_num)
                · have hs32321322 : InSquare (89/640) (239/640) (1/640) tau := by
                    convert childUL hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3741.sound htau (by
                    simp only [Batch0467.cell3741, Batch0467.tau3741, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232132 | hy3232132
                · have hs32321321 : InSquare (91/640) (237/640) (1/640) tau := by
                    convert childLR hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3740.sound htau (by
                    simp only [Batch0467.cell3740, Batch0467.tau3740, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321321 (by positivity) using 1 <;> norm_num)
                · have hs32321323 : InSquare (91/640) (239/640) (1/640) tau := by
                    convert childUR hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3742.sound htau (by
                    simp only [Batch0467.cell3742, Batch0467.tau3742, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323213 | hy323213
            · have hs3232131 : InSquare (47/320) (117/320) (1/320) tau := by
                convert childLR hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232131 | hx3232131
              · rcases le_total tau.im (117/320 : ℝ) with hy3232131 | hy3232131
                · have hs32321310 : InSquare (93/640) (233/640) (1/640) tau := by
                    convert childLL hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0466.cell3735.sound htau (by
                    simp only [Batch0466.cell3735, Batch0466.tau3735, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321310 (by positivity) using 1 <;> norm_num)
                · have hs32321312 : InSquare (93/640) (47/128) (1/640) tau := by
                    convert childUL hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3737.sound htau (by
                    simp only [Batch0467.cell3737, Batch0467.tau3737, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232131 | hy3232131
                · have hs32321311 : InSquare (19/128) (233/640) (1/640) tau := by
                    convert childLR hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3736.sound htau (by
                    simp only [Batch0467.cell3736, Batch0467.tau3736, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321311 (by positivity) using 1 <;> norm_num)
                · have hs32321313 : InSquare (19/128) (47/128) (1/640) tau := by
                    convert childUR hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3738.sound htau (by
                    simp only [Batch0467.cell3738, Batch0467.tau3738, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321313 (by positivity) using 1 <;> norm_num)
            · have hs3232133 : InSquare (47/320) (119/320) (1/320) tau := by
                convert childUR hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232133 | hx3232133
              · rcases le_total tau.im (119/320 : ℝ) with hy3232133 | hy3232133
                · have hs32321330 : InSquare (93/640) (237/640) (1/640) tau := by
                    convert childLL hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0467.cell3743.sound htau (by
                    simp only [Batch0467.cell3743, Batch0467.tau3743, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321330 (by positivity) using 1 <;> norm_num)
                · have hs32321332 : InSquare (93/640) (239/640) (1/640) tau := by
                    convert childUL hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3745.sound htau (by
                    simp only [Batch0468.cell3745, Batch0468.tau3745, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232133 | hy3232133
                · have hs32321331 : InSquare (19/128) (237/640) (1/640) tau := by
                    convert childLR hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3744.sound htau (by
                    simp only [Batch0468.cell3744, Batch0468.tau3744, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321331 (by positivity) using 1 <;> norm_num)
                · have hs32321333 : InSquare (19/128) (239/640) (1/640) tau := by
                    convert childUR hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3746.sound htau (by
                    simp only [Batch0468.cell3746, Batch0468.tau3746, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321333 (by positivity) using 1 <;> norm_num)
    · have hs32323 : InSquare (11/80) (31/80) (1/80) tau := by
        convert childUR hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32323 | hx32323
      · rcases le_total tau.im (31/80 : ℝ) with hy32323 | hy32323
        · have hs323230 : InSquare (21/160) (61/160) (1/160) tau := by
            convert childLL hs32323 hx32323 hy32323 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323230 | hx323230
          · rcases le_total tau.im (61/160 : ℝ) with hy323230 | hy323230
            · have hs3232300 : InSquare (41/320) (121/320) (1/320) tau := by
                convert childLL hs323230 hx323230 hy323230 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232300 | hx3232300
              · rcases le_total tau.im (121/320 : ℝ) with hy3232300 | hy3232300
                · have hs32323000 : InSquare (81/640) (241/640) (1/640) tau := by
                    convert childLL hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0471.cell3774.sound htau (by
                    simp only [Batch0471.cell3774, Batch0471.tau3774, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323000 (by positivity) using 1 <;> norm_num)
                · have hs32323002 : InSquare (81/640) (243/640) (1/640) tau := by
                    convert childUL hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0472.cell3776.sound htau (by
                    simp only [Batch0472.cell3776, Batch0472.tau3776, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232300 | hy3232300
                · have hs32323001 : InSquare (83/640) (241/640) (1/640) tau := by
                    convert childLR hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0471.cell3775.sound htau (by
                    simp only [Batch0471.cell3775, Batch0471.tau3775, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323001 (by positivity) using 1 <;> norm_num)
                · have hs32323003 : InSquare (83/640) (243/640) (1/640) tau := by
                    convert childUR hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0472.cell3777.sound htau (by
                    simp only [Batch0472.cell3777, Batch0472.tau3777, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323003 (by positivity) using 1 <;> norm_num)
            · have hs3232302 : InSquare (41/320) (123/320) (1/320) tau := by
                convert childUL hs323230 hx323230 hy323230 using 1 <;> norm_num
              exact (outside_3232302 htau hs3232302).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323230 | hy323230
            · have hs3232301 : InSquare (43/320) (121/320) (1/320) tau := by
                convert childLR hs323230 hx323230 hy323230 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232301 | hx3232301
              · rcases le_total tau.im (121/320 : ℝ) with hy3232301 | hy3232301
                · have hs32323010 : InSquare (17/128) (241/640) (1/640) tau := by
                    convert childLL hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact Batch0472.cell3778.sound htau (by
                    simp only [Batch0472.cell3778, Batch0472.tau3778, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323010 (by positivity) using 1 <;> norm_num)
                · have hs32323012 : InSquare (17/128) (243/640) (1/640) tau := by
                    convert childUL hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact (outside_32323012 htau hs32323012).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy3232301 | hy3232301
                · have hs32323011 : InSquare (87/640) (241/640) (1/640) tau := by
                    convert childLR hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact Batch0472.cell3779.sound htau (by
                    simp only [Batch0472.cell3779, Batch0472.tau3779, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323011 (by positivity) using 1 <;> norm_num)
                · have hs32323013 : InSquare (87/640) (243/640) (1/640) tau := by
                    convert childUR hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact (outside_32323013 htau hs32323013).elim
            · have hs3232303 : InSquare (43/320) (123/320) (1/320) tau := by
                convert childUR hs323230 hx323230 hy323230 using 1 <;> norm_num
              exact (outside_3232303 htau hs3232303).elim
        · have hs323232 : InSquare (21/160) (63/160) (1/160) tau := by
            convert childUL hs32323 hx32323 hy32323 using 1 <;> norm_num
          exact (outside_323232 htau hs323232).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32323 | hy32323
        · have hs323231 : InSquare (23/160) (61/160) (1/160) tau := by
            convert childLR hs32323 hx32323 hy32323 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323231 | hx323231
          · rcases le_total tau.im (61/160 : ℝ) with hy323231 | hy323231
            · have hs3232310 : InSquare (9/64) (121/320) (1/320) tau := by
                convert childLL hs323231 hx323231 hy323231 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232310 | hx3232310
              · rcases le_total tau.im (121/320 : ℝ) with hy3232310 | hy3232310
                · have hs32323100 : InSquare (89/640) (241/640) (1/640) tau := by
                    convert childLL hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact Batch0472.cell3780.sound htau (by
                    simp only [Batch0472.cell3780, Batch0472.tau3780, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323100 (by positivity) using 1 <;> norm_num)
                · have hs32323102 : InSquare (89/640) (243/640) (1/640) tau := by
                    convert childUL hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323102 htau hs32323102).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy3232310 | hy3232310
                · have hs32323101 : InSquare (91/640) (241/640) (1/640) tau := by
                    convert childLR hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323101 htau hs32323101).elim
                · have hs32323103 : InSquare (91/640) (243/640) (1/640) tau := by
                    convert childUR hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323103 htau hs32323103).elim
            · have hs3232312 : InSquare (9/64) (123/320) (1/320) tau := by
                convert childUL hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232312 htau hs3232312).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323231 | hy323231
            · have hs3232311 : InSquare (47/320) (121/320) (1/320) tau := by
                convert childLR hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232311 htau hs3232311).elim
            · have hs3232313 : InSquare (47/320) (123/320) (1/320) tau := by
                convert childUR hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232313 htau hs3232313).elim
        · have hs323233 : InSquare (23/160) (63/160) (1/160) tau := by
            convert childUR hs32323 hx32323 hy32323 using 1 <;> norm_num
          exact (outside_323233 htau hs323233).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232

end


