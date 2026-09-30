-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2332__8
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2332__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:19:29.219785+00:00
-- url     : https://prove2.me/theorems/90c16a37-2d16-473c-a2b2-699b684adca9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2332 (+7 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2333, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3023, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3031, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3032, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3033, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3101, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3102).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0268
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0421
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0422
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0425
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0277
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0435
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0436
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0437
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_2332222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/64) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-57/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-33/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2332 | hx2332
  · rcases le_total tau.im (3/8 : ℝ) with hy2332 | hy2332
    · have hs23320 : InSquare (-7/80) (29/80) (1/80) tau := by
        convert childLL hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23320 | hx23320
      · rcases le_total tau.im (29/80 : ℝ) with hy23320 | hy23320
        · have hs233200 : InSquare (-3/32) (57/160) (1/160) tau := by
            convert childLL hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233200 | hx233200
          · rcases le_total tau.im (57/160 : ℝ) with hy233200 | hy233200
            · have hs2332000 : InSquare (-31/320) (113/320) (1/320) tau := by
                convert childLL hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2147.sound htau (by
                simp only [Batch0268.cell2147, Batch0268.tau2147, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332000 (by positivity) using 1 <;> norm_num)
            · have hs2332002 : InSquare (-31/320) (23/64) (1/320) tau := by
                convert childUL hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2149.sound htau (by
                simp only [Batch0268.cell2149, Batch0268.tau2149, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233200 | hy233200
            · have hs2332001 : InSquare (-29/320) (113/320) (1/320) tau := by
                convert childLR hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2148.sound htau (by
                simp only [Batch0268.cell2148, Batch0268.tau2148, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332001 (by positivity) using 1 <;> norm_num)
            · have hs2332003 : InSquare (-29/320) (23/64) (1/320) tau := by
                convert childUR hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2150.sound htau (by
                simp only [Batch0268.cell2150, Batch0268.tau2150, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332003 (by positivity) using 1 <;> norm_num)
        · have hs233202 : InSquare (-3/32) (59/160) (1/160) tau := by
            convert childUL hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233202 | hx233202
          · rcases le_total tau.im (59/160 : ℝ) with hy233202 | hy233202
            · have hs2332020 : InSquare (-31/320) (117/320) (1/320) tau := by
                convert childLL hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2155.sound htau (by
                simp only [Batch0269.cell2155, Batch0269.tau2155, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332020 (by positivity) using 1 <;> norm_num)
            · have hs2332022 : InSquare (-31/320) (119/320) (1/320) tau := by
                convert childUL hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2157.sound htau (by
                simp only [Batch0269.cell2157, Batch0269.tau2157, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233202 | hy233202
            · have hs2332021 : InSquare (-29/320) (117/320) (1/320) tau := by
                convert childLR hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2156.sound htau (by
                simp only [Batch0269.cell2156, Batch0269.tau2156, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332021 (by positivity) using 1 <;> norm_num)
            · have hs2332023 : InSquare (-29/320) (119/320) (1/320) tau := by
                convert childUR hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2158.sound htau (by
                simp only [Batch0269.cell2158, Batch0269.tau2158, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23320 | hy23320
        · have hs233201 : InSquare (-13/160) (57/160) (1/160) tau := by
            convert childLR hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233201 | hx233201
          · rcases le_total tau.im (57/160 : ℝ) with hy233201 | hy233201
            · have hs2332010 : InSquare (-27/320) (113/320) (1/320) tau := by
                convert childLL hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0268.cell2151.sound htau (by
                simp only [Batch0268.cell2151, Batch0268.tau2151, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332010 (by positivity) using 1 <;> norm_num)
            · have hs2332012 : InSquare (-27/320) (23/64) (1/320) tau := by
                convert childUL hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2153.sound htau (by
                simp only [Batch0269.cell2153, Batch0269.tau2153, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233201 | hy233201
            · have hs2332011 : InSquare (-5/64) (113/320) (1/320) tau := by
                convert childLR hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2152.sound htau (by
                simp only [Batch0269.cell2152, Batch0269.tau2152, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332011 (by positivity) using 1 <;> norm_num)
            · have hs2332013 : InSquare (-5/64) (23/64) (1/320) tau := by
                convert childUR hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2154.sound htau (by
                simp only [Batch0269.cell2154, Batch0269.tau2154, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332013 (by positivity) using 1 <;> norm_num)
        · have hs233203 : InSquare (-13/160) (59/160) (1/160) tau := by
            convert childUR hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233203 | hx233203
          · rcases le_total tau.im (59/160 : ℝ) with hy233203 | hy233203
            · have hs2332030 : InSquare (-27/320) (117/320) (1/320) tau := by
                convert childLL hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0269.cell2159.sound htau (by
                simp only [Batch0269.cell2159, Batch0269.tau2159, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332030 (by positivity) using 1 <;> norm_num)
            · have hs2332032 : InSquare (-27/320) (119/320) (1/320) tau := by
                convert childUL hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2161.sound htau (by
                simp only [Batch0270.cell2161, Batch0270.tau2161, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233203 | hy233203
            · have hs2332031 : InSquare (-5/64) (117/320) (1/320) tau := by
                convert childLR hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2160.sound htau (by
                simp only [Batch0270.cell2160, Batch0270.tau2160, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332031 (by positivity) using 1 <;> norm_num)
            · have hs2332033 : InSquare (-5/64) (119/320) (1/320) tau := by
                convert childUR hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2162.sound htau (by
                simp only [Batch0270.cell2162, Batch0270.tau2162, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332033 (by positivity) using 1 <;> norm_num)
    · have hs23322 : InSquare (-7/80) (31/80) (1/80) tau := by
        convert childUL hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23322 | hx23322
      · rcases le_total tau.im (31/80 : ℝ) with hy23322 | hy23322
        · have hs233220 : InSquare (-3/32) (61/160) (1/160) tau := by
            convert childLL hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233220 | hx233220
          · rcases le_total tau.im (61/160 : ℝ) with hy233220 | hy233220
            · have hs2332200 : InSquare (-31/320) (121/320) (1/320) tau := by
                convert childLL hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332200 | hx2332200
              · rcases le_total tau.im (121/320 : ℝ) with hy2332200 | hy2332200
                · have hs23322000 : InSquare (-63/640) (241/640) (1/640) tau := by
                    convert childLL hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3361.sound htau (by
                    simp only [Batch0420.cell3361, Batch0420.tau3361, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322000 (by positivity) using 1 <;> norm_num)
                · have hs23322002 : InSquare (-63/640) (243/640) (1/640) tau := by
                    convert childUL hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3363.sound htau (by
                    simp only [Batch0420.cell3363, Batch0420.tau3363, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332200 | hy2332200
                · have hs23322001 : InSquare (-61/640) (241/640) (1/640) tau := by
                    convert childLR hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3362.sound htau (by
                    simp only [Batch0420.cell3362, Batch0420.tau3362, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322001 (by positivity) using 1 <;> norm_num)
                · have hs23322003 : InSquare (-61/640) (243/640) (1/640) tau := by
                    convert childUR hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3364.sound htau (by
                    simp only [Batch0420.cell3364, Batch0420.tau3364, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322003 (by positivity) using 1 <;> norm_num)
            · have hs2332202 : InSquare (-31/320) (123/320) (1/320) tau := by
                convert childUL hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332202 | hx2332202
              · rcases le_total tau.im (123/320 : ℝ) with hy2332202 | hy2332202
                · have hs23322020 : InSquare (-63/640) (49/128) (1/640) tau := by
                    convert childLL hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3369.sound htau (by
                    simp only [Batch0421.cell3369, Batch0421.tau3369, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322020 (by positivity) using 1 <;> norm_num)
                · have hs23322022 : InSquare (-63/640) (247/640) (1/640) tau := by
                    convert childUL hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3371.sound htau (by
                    simp only [Batch0421.cell3371, Batch0421.tau3371, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332202 | hy2332202
                · have hs23322021 : InSquare (-61/640) (49/128) (1/640) tau := by
                    convert childLR hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3370.sound htau (by
                    simp only [Batch0421.cell3370, Batch0421.tau3370, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322021 (by positivity) using 1 <;> norm_num)
                · have hs23322023 : InSquare (-61/640) (247/640) (1/640) tau := by
                    convert childUR hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3372.sound htau (by
                    simp only [Batch0421.cell3372, Batch0421.tau3372, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233220 | hy233220
            · have hs2332201 : InSquare (-29/320) (121/320) (1/320) tau := by
                convert childLR hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332201 | hx2332201
              · rcases le_total tau.im (121/320 : ℝ) with hy2332201 | hy2332201
                · have hs23322010 : InSquare (-59/640) (241/640) (1/640) tau := by
                    convert childLL hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3365.sound htau (by
                    simp only [Batch0420.cell3365, Batch0420.tau3365, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322010 (by positivity) using 1 <;> norm_num)
                · have hs23322012 : InSquare (-59/640) (243/640) (1/640) tau := by
                    convert childUL hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3367.sound htau (by
                    simp only [Batch0420.cell3367, Batch0420.tau3367, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332201 | hy2332201
                · have hs23322011 : InSquare (-57/640) (241/640) (1/640) tau := by
                    convert childLR hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3366.sound htau (by
                    simp only [Batch0420.cell3366, Batch0420.tau3366, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322011 (by positivity) using 1 <;> norm_num)
                · have hs23322013 : InSquare (-57/640) (243/640) (1/640) tau := by
                    convert childUR hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0421.cell3368.sound htau (by
                    simp only [Batch0421.cell3368, Batch0421.tau3368, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322013 (by positivity) using 1 <;> norm_num)
            · have hs2332203 : InSquare (-29/320) (123/320) (1/320) tau := by
                convert childUR hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332203 | hx2332203
              · rcases le_total tau.im (123/320 : ℝ) with hy2332203 | hy2332203
                · have hs23322030 : InSquare (-59/640) (49/128) (1/640) tau := by
                    convert childLL hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3373.sound htau (by
                    simp only [Batch0421.cell3373, Batch0421.tau3373, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322030 (by positivity) using 1 <;> norm_num)
                · have hs23322032 : InSquare (-59/640) (247/640) (1/640) tau := by
                    convert childUL hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3375.sound htau (by
                    simp only [Batch0421.cell3375, Batch0421.tau3375, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332203 | hy2332203
                · have hs23322031 : InSquare (-57/640) (49/128) (1/640) tau := by
                    convert childLR hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3374.sound htau (by
                    simp only [Batch0421.cell3374, Batch0421.tau3374, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322031 (by positivity) using 1 <;> norm_num)
                · have hs23322033 : InSquare (-57/640) (247/640) (1/640) tau := by
                    convert childUR hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0422.cell3376.sound htau (by
                    simp only [Batch0422.cell3376, Batch0422.tau3376, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322033 (by positivity) using 1 <;> norm_num)
        · have hs233222 : InSquare (-3/32) (63/160) (1/160) tau := by
            convert childUL hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233222 | hx233222
          · rcases le_total tau.im (63/160 : ℝ) with hy233222 | hy233222
            · have hs2332220 : InSquare (-31/320) (25/64) (1/320) tau := by
                convert childLL hs233222 hx233222 hy233222 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332220 | hx2332220
              · rcases le_total tau.im (25/64 : ℝ) with hy2332220 | hy2332220
                · have hs23322200 : InSquare (-63/640) (249/640) (1/640) tau := by
                    convert childLL hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact Batch0424.cell3393.sound htau (by
                    simp only [Batch0424.cell3393, Batch0424.tau3393, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322200 (by positivity) using 1 <;> norm_num)
                · have hs23322202 : InSquare (-63/640) (251/640) (1/640) tau := by
                    convert childUL hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact (outside_23322202 htau hs23322202).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy2332220 | hy2332220
                · have hs23322201 : InSquare (-61/640) (249/640) (1/640) tau := by
                    convert childLR hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact Batch0424.cell3394.sound htau (by
                    simp only [Batch0424.cell3394, Batch0424.tau3394, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322201 (by positivity) using 1 <;> norm_num)
                · have hs23322203 : InSquare (-61/640) (251/640) (1/640) tau := by
                    convert childUR hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact (outside_23322203 htau hs23322203).elim
            · have hs2332222 : InSquare (-31/320) (127/320) (1/320) tau := by
                convert childUL hs233222 hx233222 hy233222 using 1 <;> norm_num
              exact (outside_2332222 htau hs2332222).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233222 | hy233222
            · have hs2332221 : InSquare (-29/320) (25/64) (1/320) tau := by
                convert childLR hs233222 hx233222 hy233222 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332221 | hx2332221
              · rcases le_total tau.im (25/64 : ℝ) with hy2332221 | hy2332221
                · have hs23322210 : InSquare (-59/640) (249/640) (1/640) tau := by
                    convert childLL hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact Batch0424.cell3395.sound htau (by
                    simp only [Batch0424.cell3395, Batch0424.tau3395, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322210 (by positivity) using 1 <;> norm_num)
                · have hs23322212 : InSquare (-59/640) (251/640) (1/640) tau := by
                    convert childUL hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact (outside_23322212 htau hs23322212).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy2332221 | hy2332221
                · have hs23322211 : InSquare (-57/640) (249/640) (1/640) tau := by
                    convert childLR hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact Batch0424.cell3396.sound htau (by
                    simp only [Batch0424.cell3396, Batch0424.tau3396, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322211 (by positivity) using 1 <;> norm_num)
                · have hs23322213 : InSquare (-57/640) (251/640) (1/640) tau := by
                    convert childUR hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact (outside_23322213 htau hs23322213).elim
            · have hs2332223 : InSquare (-29/320) (127/320) (1/320) tau := by
                convert childUR hs233222 hx233222 hy233222 using 1 <;> norm_num
              exact (outside_2332223 htau hs2332223).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23322 | hy23322
        · have hs233221 : InSquare (-13/160) (61/160) (1/160) tau := by
            convert childLR hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233221 | hx233221
          · rcases le_total tau.im (61/160 : ℝ) with hy233221 | hy233221
            · have hs2332210 : InSquare (-27/320) (121/320) (1/320) tau := by
                convert childLL hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332210 | hx2332210
              · rcases le_total tau.im (121/320 : ℝ) with hy2332210 | hy2332210
                · have hs23322100 : InSquare (-11/128) (241/640) (1/640) tau := by
                    convert childLL hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3377.sound htau (by
                    simp only [Batch0422.cell3377, Batch0422.tau3377, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322100 (by positivity) using 1 <;> norm_num)
                · have hs23322102 : InSquare (-11/128) (243/640) (1/640) tau := by
                    convert childUL hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3379.sound htau (by
                    simp only [Batch0422.cell3379, Batch0422.tau3379, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332210 | hy2332210
                · have hs23322101 : InSquare (-53/640) (241/640) (1/640) tau := by
                    convert childLR hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3378.sound htau (by
                    simp only [Batch0422.cell3378, Batch0422.tau3378, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322101 (by positivity) using 1 <;> norm_num)
                · have hs23322103 : InSquare (-53/640) (243/640) (1/640) tau := by
                    convert childUR hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3380.sound htau (by
                    simp only [Batch0422.cell3380, Batch0422.tau3380, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322103 (by positivity) using 1 <;> norm_num)
            · have hs2332212 : InSquare (-27/320) (123/320) (1/320) tau := by
                convert childUL hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332212 | hx2332212
              · rcases le_total tau.im (123/320 : ℝ) with hy2332212 | hy2332212
                · have hs23322120 : InSquare (-11/128) (49/128) (1/640) tau := by
                    convert childLL hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3385.sound htau (by
                    simp only [Batch0423.cell3385, Batch0423.tau3385, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322120 (by positivity) using 1 <;> norm_num)
                · have hs23322122 : InSquare (-11/128) (247/640) (1/640) tau := by
                    convert childUL hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3387.sound htau (by
                    simp only [Batch0423.cell3387, Batch0423.tau3387, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332212 | hy2332212
                · have hs23322121 : InSquare (-53/640) (49/128) (1/640) tau := by
                    convert childLR hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3386.sound htau (by
                    simp only [Batch0423.cell3386, Batch0423.tau3386, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322121 (by positivity) using 1 <;> norm_num)
                · have hs23322123 : InSquare (-53/640) (247/640) (1/640) tau := by
                    convert childUR hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3388.sound htau (by
                    simp only [Batch0423.cell3388, Batch0423.tau3388, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233221 | hy233221
            · have hs2332211 : InSquare (-5/64) (121/320) (1/320) tau := by
                convert childLR hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332211 | hx2332211
              · rcases le_total tau.im (121/320 : ℝ) with hy2332211 | hy2332211
                · have hs23322110 : InSquare (-51/640) (241/640) (1/640) tau := by
                    convert childLL hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3381.sound htau (by
                    simp only [Batch0422.cell3381, Batch0422.tau3381, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322110 (by positivity) using 1 <;> norm_num)
                · have hs23322112 : InSquare (-51/640) (243/640) (1/640) tau := by
                    convert childUL hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3383.sound htau (by
                    simp only [Batch0422.cell3383, Batch0422.tau3383, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332211 | hy2332211
                · have hs23322111 : InSquare (-49/640) (241/640) (1/640) tau := by
                    convert childLR hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3382.sound htau (by
                    simp only [Batch0422.cell3382, Batch0422.tau3382, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322111 (by positivity) using 1 <;> norm_num)
                · have hs23322113 : InSquare (-49/640) (243/640) (1/640) tau := by
                    convert childUR hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0423.cell3384.sound htau (by
                    simp only [Batch0423.cell3384, Batch0423.tau3384, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322113 (by positivity) using 1 <;> norm_num)
            · have hs2332213 : InSquare (-5/64) (123/320) (1/320) tau := by
                convert childUR hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332213 | hx2332213
              · rcases le_total tau.im (123/320 : ℝ) with hy2332213 | hy2332213
                · have hs23322130 : InSquare (-51/640) (49/128) (1/640) tau := by
                    convert childLL hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3389.sound htau (by
                    simp only [Batch0423.cell3389, Batch0423.tau3389, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322130 (by positivity) using 1 <;> norm_num)
                · have hs23322132 : InSquare (-51/640) (247/640) (1/640) tau := by
                    convert childUL hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3391.sound htau (by
                    simp only [Batch0423.cell3391, Batch0423.tau3391, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332213 | hy2332213
                · have hs23322131 : InSquare (-49/640) (49/128) (1/640) tau := by
                    convert childLR hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3390.sound htau (by
                    simp only [Batch0423.cell3390, Batch0423.tau3390, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322131 (by positivity) using 1 <;> norm_num)
                · have hs23322133 : InSquare (-49/640) (247/640) (1/640) tau := by
                    convert childUR hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0424.cell3392.sound htau (by
                    simp only [Batch0424.cell3392, Batch0424.tau3392, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322133 (by positivity) using 1 <;> norm_num)
        · have hs233223 : InSquare (-13/160) (63/160) (1/160) tau := by
            convert childUR hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233223 | hx233223
          · rcases le_total tau.im (63/160 : ℝ) with hy233223 | hy233223
            · have hs2332230 : InSquare (-27/320) (25/64) (1/320) tau := by
                convert childLL hs233223 hx233223 hy233223 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332230 | hx2332230
              · rcases le_total tau.im (25/64 : ℝ) with hy2332230 | hy2332230
                · have hs23322300 : InSquare (-11/128) (249/640) (1/640) tau := by
                    convert childLL hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3397.sound htau (by
                    simp only [Batch0424.cell3397, Batch0424.tau3397, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322300 (by positivity) using 1 <;> norm_num)
                · have hs23322302 : InSquare (-11/128) (251/640) (1/640) tau := by
                    convert childUL hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3399.sound htau (by
                    simp only [Batch0424.cell3399, Batch0424.tau3399, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332230 | hy2332230
                · have hs23322301 : InSquare (-53/640) (249/640) (1/640) tau := by
                    convert childLR hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3398.sound htau (by
                    simp only [Batch0424.cell3398, Batch0424.tau3398, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322301 (by positivity) using 1 <;> norm_num)
                · have hs23322303 : InSquare (-53/640) (251/640) (1/640) tau := by
                    convert childUR hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0425.cell3400.sound htau (by
                    simp only [Batch0425.cell3400, Batch0425.tau3400, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322303 (by positivity) using 1 <;> norm_num)
            · have hs2332232 : InSquare (-27/320) (127/320) (1/320) tau := by
                convert childUL hs233223 hx233223 hy233223 using 1 <;> norm_num
              exact (outside_2332232 htau hs2332232).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233223 | hy233223
            · have hs2332231 : InSquare (-5/64) (25/64) (1/320) tau := by
                convert childLR hs233223 hx233223 hy233223 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332231 | hx2332231
              · rcases le_total tau.im (25/64 : ℝ) with hy2332231 | hy2332231
                · have hs23322310 : InSquare (-51/640) (249/640) (1/640) tau := by
                    convert childLL hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3401.sound htau (by
                    simp only [Batch0425.cell3401, Batch0425.tau3401, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322310 (by positivity) using 1 <;> norm_num)
                · have hs23322312 : InSquare (-51/640) (251/640) (1/640) tau := by
                    convert childUL hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3403.sound htau (by
                    simp only [Batch0425.cell3403, Batch0425.tau3403, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332231 | hy2332231
                · have hs23322311 : InSquare (-49/640) (249/640) (1/640) tau := by
                    convert childLR hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3402.sound htau (by
                    simp only [Batch0425.cell3402, Batch0425.tau3402, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322311 (by positivity) using 1 <;> norm_num)
                · have hs23322313 : InSquare (-49/640) (251/640) (1/640) tau := by
                    convert childUR hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3404.sound htau (by
                    simp only [Batch0425.cell3404, Batch0425.tau3404, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322313 (by positivity) using 1 <;> norm_num)
            · have hs2332233 : InSquare (-5/64) (127/320) (1/320) tau := by
                convert childUR hs233223 hx233223 hy233223 using 1 <;> norm_num
              exact (outside_2332233 htau hs2332233).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2332 | hy2332
    · have hs23321 : InSquare (-1/16) (29/80) (1/80) tau := by
        convert childLR hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23321 | hx23321
      · rcases le_total tau.im (29/80 : ℝ) with hy23321 | hy23321
        · have hs233210 : InSquare (-11/160) (57/160) (1/160) tau := by
            convert childLL hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233210 | hx233210
          · rcases le_total tau.im (57/160 : ℝ) with hy233210 | hy233210
            · have hs2332100 : InSquare (-23/320) (113/320) (1/320) tau := by
                convert childLL hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2163.sound htau (by
                simp only [Batch0270.cell2163, Batch0270.tau2163, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332100 (by positivity) using 1 <;> norm_num)
            · have hs2332102 : InSquare (-23/320) (23/64) (1/320) tau := by
                convert childUL hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2165.sound htau (by
                simp only [Batch0270.cell2165, Batch0270.tau2165, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233210 | hy233210
            · have hs2332101 : InSquare (-21/320) (113/320) (1/320) tau := by
                convert childLR hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2164.sound htau (by
                simp only [Batch0270.cell2164, Batch0270.tau2164, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332101 (by positivity) using 1 <;> norm_num)
            · have hs2332103 : InSquare (-21/320) (23/64) (1/320) tau := by
                convert childUR hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2166.sound htau (by
                simp only [Batch0270.cell2166, Batch0270.tau2166, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332103 (by positivity) using 1 <;> norm_num)
        · have hs233212 : InSquare (-11/160) (59/160) (1/160) tau := by
            convert childUL hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233212 | hx233212
          · rcases le_total tau.im (59/160 : ℝ) with hy233212 | hy233212
            · have hs2332120 : InSquare (-23/320) (117/320) (1/320) tau := by
                convert childLL hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2171.sound htau (by
                simp only [Batch0271.cell2171, Batch0271.tau2171, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332120 (by positivity) using 1 <;> norm_num)
            · have hs2332122 : InSquare (-23/320) (119/320) (1/320) tau := by
                convert childUL hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2173.sound htau (by
                simp only [Batch0271.cell2173, Batch0271.tau2173, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233212 | hy233212
            · have hs2332121 : InSquare (-21/320) (117/320) (1/320) tau := by
                convert childLR hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2172.sound htau (by
                simp only [Batch0271.cell2172, Batch0271.tau2172, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332121 (by positivity) using 1 <;> norm_num)
            · have hs2332123 : InSquare (-21/320) (119/320) (1/320) tau := by
                convert childUR hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2174.sound htau (by
                simp only [Batch0271.cell2174, Batch0271.tau2174, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23321 | hy23321
        · have hs233211 : InSquare (-9/160) (57/160) (1/160) tau := by
            convert childLR hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233211 | hx233211
          · rcases le_total tau.im (57/160 : ℝ) with hy233211 | hy233211
            · have hs2332110 : InSquare (-19/320) (113/320) (1/320) tau := by
                convert childLL hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0270.cell2167.sound htau (by
                simp only [Batch0270.cell2167, Batch0270.tau2167, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332110 (by positivity) using 1 <;> norm_num)
            · have hs2332112 : InSquare (-19/320) (23/64) (1/320) tau := by
                convert childUL hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2169.sound htau (by
                simp only [Batch0271.cell2169, Batch0271.tau2169, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233211 | hy233211
            · have hs2332111 : InSquare (-17/320) (113/320) (1/320) tau := by
                convert childLR hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2168.sound htau (by
                simp only [Batch0271.cell2168, Batch0271.tau2168, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332111 (by positivity) using 1 <;> norm_num)
            · have hs2332113 : InSquare (-17/320) (23/64) (1/320) tau := by
                convert childUR hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2170.sound htau (by
                simp only [Batch0271.cell2170, Batch0271.tau2170, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332113 (by positivity) using 1 <;> norm_num)
        · have hs233213 : InSquare (-9/160) (59/160) (1/160) tau := by
            convert childUR hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233213 | hx233213
          · rcases le_total tau.im (59/160 : ℝ) with hy233213 | hy233213
            · have hs2332130 : InSquare (-19/320) (117/320) (1/320) tau := by
                convert childLL hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0271.cell2175.sound htau (by
                simp only [Batch0271.cell2175, Batch0271.tau2175, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332130 (by positivity) using 1 <;> norm_num)
            · have hs2332132 : InSquare (-19/320) (119/320) (1/320) tau := by
                convert childUL hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2177.sound htau (by
                simp only [Batch0272.cell2177, Batch0272.tau2177, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233213 | hy233213
            · have hs2332131 : InSquare (-17/320) (117/320) (1/320) tau := by
                convert childLR hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2176.sound htau (by
                simp only [Batch0272.cell2176, Batch0272.tau2176, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332131 (by positivity) using 1 <;> norm_num)
            · have hs2332133 : InSquare (-17/320) (119/320) (1/320) tau := by
                convert childUR hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2178.sound htau (by
                simp only [Batch0272.cell2178, Batch0272.tau2178, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332133 (by positivity) using 1 <;> norm_num)
    · have hs23323 : InSquare (-1/16) (31/80) (1/80) tau := by
        convert childUR hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23323 | hx23323
      · rcases le_total tau.im (31/80 : ℝ) with hy23323 | hy23323
        · have hs233230 : InSquare (-11/160) (61/160) (1/160) tau := by
            convert childLL hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233230 | hx233230
          · rcases le_total tau.im (61/160 : ℝ) with hy233230 | hy233230
            · have hs2332300 : InSquare (-23/320) (121/320) (1/320) tau := by
                convert childLL hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332300 | hx2332300
              · rcases le_total tau.im (121/320 : ℝ) with hy2332300 | hy2332300
                · have hs23323000 : InSquare (-47/640) (241/640) (1/640) tau := by
                    convert childLL hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3405.sound htau (by
                    simp only [Batch0425.cell3405, Batch0425.tau3405, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323000 (by positivity) using 1 <;> norm_num)
                · have hs23323002 : InSquare (-47/640) (243/640) (1/640) tau := by
                    convert childUL hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3407.sound htau (by
                    simp only [Batch0425.cell3407, Batch0425.tau3407, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332300 | hy2332300
                · have hs23323001 : InSquare (-9/128) (241/640) (1/640) tau := by
                    convert childLR hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3406.sound htau (by
                    simp only [Batch0425.cell3406, Batch0425.tau3406, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323001 (by positivity) using 1 <;> norm_num)
                · have hs23323003 : InSquare (-9/128) (243/640) (1/640) tau := by
                    convert childUR hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0426.cell3408.sound htau (by
                    simp only [Batch0426.cell3408, Batch0426.tau3408, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323003 (by positivity) using 1 <;> norm_num)
            · have hs2332302 : InSquare (-23/320) (123/320) (1/320) tau := by
                convert childUL hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332302 | hx2332302
              · rcases le_total tau.im (123/320 : ℝ) with hy2332302 | hy2332302
                · have hs23323020 : InSquare (-47/640) (49/128) (1/640) tau := by
                    convert childLL hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3409.sound htau (by
                    simp only [Batch0426.cell3409, Batch0426.tau3409, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323020 (by positivity) using 1 <;> norm_num)
                · have hs23323022 : InSquare (-47/640) (247/640) (1/640) tau := by
                    convert childUL hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3411.sound htau (by
                    simp only [Batch0426.cell3411, Batch0426.tau3411, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332302 | hy2332302
                · have hs23323021 : InSquare (-9/128) (49/128) (1/640) tau := by
                    convert childLR hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3410.sound htau (by
                    simp only [Batch0426.cell3410, Batch0426.tau3410, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323021 (by positivity) using 1 <;> norm_num)
                · have hs23323023 : InSquare (-9/128) (247/640) (1/640) tau := by
                    convert childUR hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3412.sound htau (by
                    simp only [Batch0426.cell3412, Batch0426.tau3412, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233230 | hy233230
            · have hs2332301 : InSquare (-21/320) (121/320) (1/320) tau := by
                convert childLR hs233230 hx233230 hy233230 using 1 <;> norm_num
              exact Batch0272.cell2179.sound htau (by
                simp only [Batch0272.cell2179, Batch0272.tau2179, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332301 (by positivity) using 1 <;> norm_num)
            · have hs2332303 : InSquare (-21/320) (123/320) (1/320) tau := by
                convert childUR hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332303 | hx2332303
              · rcases le_total tau.im (123/320 : ℝ) with hy2332303 | hy2332303
                · have hs23323030 : InSquare (-43/640) (49/128) (1/640) tau := by
                    convert childLL hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3413.sound htau (by
                    simp only [Batch0426.cell3413, Batch0426.tau3413, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323030 (by positivity) using 1 <;> norm_num)
                · have hs23323032 : InSquare (-43/640) (247/640) (1/640) tau := by
                    convert childUL hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3415.sound htau (by
                    simp only [Batch0426.cell3415, Batch0426.tau3415, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332303 | hy2332303
                · have hs23323031 : InSquare (-41/640) (49/128) (1/640) tau := by
                    convert childLR hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3414.sound htau (by
                    simp only [Batch0426.cell3414, Batch0426.tau3414, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323031 (by positivity) using 1 <;> norm_num)
                · have hs23323033 : InSquare (-41/640) (247/640) (1/640) tau := by
                    convert childUR hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0427.cell3416.sound htau (by
                    simp only [Batch0427.cell3416, Batch0427.tau3416, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323033 (by positivity) using 1 <;> norm_num)
        · have hs233232 : InSquare (-11/160) (63/160) (1/160) tau := by
            convert childUL hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233232 | hx233232
          · rcases le_total tau.im (63/160 : ℝ) with hy233232 | hy233232
            · have hs2332320 : InSquare (-23/320) (25/64) (1/320) tau := by
                convert childLL hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332320 | hx2332320
              · rcases le_total tau.im (25/64 : ℝ) with hy2332320 | hy2332320
                · have hs23323200 : InSquare (-47/640) (249/640) (1/640) tau := by
                    convert childLL hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3425.sound htau (by
                    simp only [Batch0428.cell3425, Batch0428.tau3425, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323200 (by positivity) using 1 <;> norm_num)
                · have hs23323202 : InSquare (-47/640) (251/640) (1/640) tau := by
                    convert childUL hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3427.sound htau (by
                    simp only [Batch0428.cell3427, Batch0428.tau3427, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332320 | hy2332320
                · have hs23323201 : InSquare (-9/128) (249/640) (1/640) tau := by
                    convert childLR hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3426.sound htau (by
                    simp only [Batch0428.cell3426, Batch0428.tau3426, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323201 (by positivity) using 1 <;> norm_num)
                · have hs23323203 : InSquare (-9/128) (251/640) (1/640) tau := by
                    convert childUR hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3428.sound htau (by
                    simp only [Batch0428.cell3428, Batch0428.tau3428, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323203 (by positivity) using 1 <;> norm_num)
            · have hs2332322 : InSquare (-23/320) (127/320) (1/320) tau := by
                convert childUL hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332322 | hx2332322
              · rcases le_total tau.im (127/320 : ℝ) with hy2332322 | hy2332322
                · have hs23323220 : InSquare (-47/640) (253/640) (1/640) tau := by
                    convert childLL hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323220 htau hs23323220).elim
                · have hs23323222 : InSquare (-47/640) (51/128) (1/640) tau := by
                    convert childUL hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323222 htau hs23323222).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332322 | hy2332322
                · have hs23323221 : InSquare (-9/128) (253/640) (1/640) tau := by
                    convert childLR hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact Batch0429.cell3433.sound htau (by
                    simp only [Batch0429.cell3433, Batch0429.tau3433, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323221 (by positivity) using 1 <;> norm_num)
                · have hs23323223 : InSquare (-9/128) (51/128) (1/640) tau := by
                    convert childUR hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323223 htau hs23323223).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233232 | hy233232
            · have hs2332321 : InSquare (-21/320) (25/64) (1/320) tau := by
                convert childLR hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332321 | hx2332321
              · rcases le_total tau.im (25/64 : ℝ) with hy2332321 | hy2332321
                · have hs23323210 : InSquare (-43/640) (249/640) (1/640) tau := by
                    convert childLL hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3429.sound htau (by
                    simp only [Batch0428.cell3429, Batch0428.tau3429, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323210 (by positivity) using 1 <;> norm_num)
                · have hs23323212 : InSquare (-43/640) (251/640) (1/640) tau := by
                    convert childUL hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3431.sound htau (by
                    simp only [Batch0428.cell3431, Batch0428.tau3431, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332321 | hy2332321
                · have hs23323211 : InSquare (-41/640) (249/640) (1/640) tau := by
                    convert childLR hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3430.sound htau (by
                    simp only [Batch0428.cell3430, Batch0428.tau3430, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323211 (by positivity) using 1 <;> norm_num)
                · have hs23323213 : InSquare (-41/640) (251/640) (1/640) tau := by
                    convert childUR hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0429.cell3432.sound htau (by
                    simp only [Batch0429.cell3432, Batch0429.tau3432, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323213 (by positivity) using 1 <;> norm_num)
            · have hs2332323 : InSquare (-21/320) (127/320) (1/320) tau := by
                convert childUR hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332323 | hx2332323
              · rcases le_total tau.im (127/320 : ℝ) with hy2332323 | hy2332323
                · have hs23323230 : InSquare (-43/640) (253/640) (1/640) tau := by
                    convert childLL hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact Batch0429.cell3434.sound htau (by
                    simp only [Batch0429.cell3434, Batch0429.tau3434, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323230 (by positivity) using 1 <;> norm_num)
                · have hs23323232 : InSquare (-43/640) (51/128) (1/640) tau := by
                    convert childUL hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact (outside_23323232 htau hs23323232).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332323 | hy2332323
                · have hs23323231 : InSquare (-41/640) (253/640) (1/640) tau := by
                    convert childLR hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact Batch0429.cell3435.sound htau (by
                    simp only [Batch0429.cell3435, Batch0429.tau3435, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323231 (by positivity) using 1 <;> norm_num)
                · have hs23323233 : InSquare (-41/640) (51/128) (1/640) tau := by
                    convert childUR hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact (outside_23323233 htau hs23323233).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23323 | hy23323
        · have hs233231 : InSquare (-9/160) (61/160) (1/160) tau := by
            convert childLR hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233231 | hx233231
          · rcases le_total tau.im (61/160 : ℝ) with hy233231 | hy233231
            · have hs2332310 : InSquare (-19/320) (121/320) (1/320) tau := by
                convert childLL hs233231 hx233231 hy233231 using 1 <;> norm_num
              exact Batch0272.cell2180.sound htau (by
                simp only [Batch0272.cell2180, Batch0272.tau2180, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332310 (by positivity) using 1 <;> norm_num)
            · have hs2332312 : InSquare (-19/320) (123/320) (1/320) tau := by
                convert childUL hs233231 hx233231 hy233231 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332312 | hx2332312
              · rcases le_total tau.im (123/320 : ℝ) with hy2332312 | hy2332312
                · have hs23323120 : InSquare (-39/640) (49/128) (1/640) tau := by
                    convert childLL hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3417.sound htau (by
                    simp only [Batch0427.cell3417, Batch0427.tau3417, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323120 (by positivity) using 1 <;> norm_num)
                · have hs23323122 : InSquare (-39/640) (247/640) (1/640) tau := by
                    convert childUL hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3419.sound htau (by
                    simp only [Batch0427.cell3419, Batch0427.tau3419, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332312 | hy2332312
                · have hs23323121 : InSquare (-37/640) (49/128) (1/640) tau := by
                    convert childLR hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3418.sound htau (by
                    simp only [Batch0427.cell3418, Batch0427.tau3418, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323121 (by positivity) using 1 <;> norm_num)
                · have hs23323123 : InSquare (-37/640) (247/640) (1/640) tau := by
                    convert childUR hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3420.sound htau (by
                    simp only [Batch0427.cell3420, Batch0427.tau3420, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233231 | hy233231
            · have hs2332311 : InSquare (-17/320) (121/320) (1/320) tau := by
                convert childLR hs233231 hx233231 hy233231 using 1 <;> norm_num
              exact Batch0272.cell2181.sound htau (by
                simp only [Batch0272.cell2181, Batch0272.tau2181, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332311 (by positivity) using 1 <;> norm_num)
            · have hs2332313 : InSquare (-17/320) (123/320) (1/320) tau := by
                convert childUR hs233231 hx233231 hy233231 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332313 | hx2332313
              · rcases le_total tau.im (123/320 : ℝ) with hy2332313 | hy2332313
                · have hs23323130 : InSquare (-7/128) (49/128) (1/640) tau := by
                    convert childLL hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3421.sound htau (by
                    simp only [Batch0427.cell3421, Batch0427.tau3421, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323130 (by positivity) using 1 <;> norm_num)
                · have hs23323132 : InSquare (-7/128) (247/640) (1/640) tau := by
                    convert childUL hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3423.sound htau (by
                    simp only [Batch0427.cell3423, Batch0427.tau3423, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332313 | hy2332313
                · have hs23323131 : InSquare (-33/640) (49/128) (1/640) tau := by
                    convert childLR hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3422.sound htau (by
                    simp only [Batch0427.cell3422, Batch0427.tau3422, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323131 (by positivity) using 1 <;> norm_num)
                · have hs23323133 : InSquare (-33/640) (247/640) (1/640) tau := by
                    convert childUR hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0428.cell3424.sound htau (by
                    simp only [Batch0428.cell3424, Batch0428.tau3424, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323133 (by positivity) using 1 <;> norm_num)
        · have hs233233 : InSquare (-9/160) (63/160) (1/160) tau := by
            convert childUR hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233233 | hx233233
          · rcases le_total tau.im (63/160 : ℝ) with hy233233 | hy233233
            · have hs2332330 : InSquare (-19/320) (25/64) (1/320) tau := by
                convert childLL hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332330 | hx2332330
              · rcases le_total tau.im (25/64 : ℝ) with hy2332330 | hy2332330
                · have hs23323300 : InSquare (-39/640) (249/640) (1/640) tau := by
                    convert childLL hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3436.sound htau (by
                    simp only [Batch0429.cell3436, Batch0429.tau3436, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323300 (by positivity) using 1 <;> norm_num)
                · have hs23323302 : InSquare (-39/640) (251/640) (1/640) tau := by
                    convert childUL hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3438.sound htau (by
                    simp only [Batch0429.cell3438, Batch0429.tau3438, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332330 | hy2332330
                · have hs23323301 : InSquare (-37/640) (249/640) (1/640) tau := by
                    convert childLR hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3437.sound htau (by
                    simp only [Batch0429.cell3437, Batch0429.tau3437, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323301 (by positivity) using 1 <;> norm_num)
                · have hs23323303 : InSquare (-37/640) (251/640) (1/640) tau := by
                    convert childUR hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3439.sound htau (by
                    simp only [Batch0429.cell3439, Batch0429.tau3439, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323303 (by positivity) using 1 <;> norm_num)
            · have hs2332332 : InSquare (-19/320) (127/320) (1/320) tau := by
                convert childUL hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332332 | hx2332332
              · rcases le_total tau.im (127/320 : ℝ) with hy2332332 | hy2332332
                · have hs23323320 : InSquare (-39/640) (253/640) (1/640) tau := by
                    convert childLL hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact Batch0430.cell3444.sound htau (by
                    simp only [Batch0430.cell3444, Batch0430.tau3444, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323320 (by positivity) using 1 <;> norm_num)
                · have hs23323322 : InSquare (-39/640) (51/128) (1/640) tau := by
                    convert childUL hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact (outside_23323322 htau hs23323322).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332332 | hy2332332
                · have hs23323321 : InSquare (-37/640) (253/640) (1/640) tau := by
                    convert childLR hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact Batch0430.cell3445.sound htau (by
                    simp only [Batch0430.cell3445, Batch0430.tau3445, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323321 (by positivity) using 1 <;> norm_num)
                · have hs23323323 : InSquare (-37/640) (51/128) (1/640) tau := by
                    convert childUR hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact (outside_23323323 htau hs23323323).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233233 | hy233233
            · have hs2332331 : InSquare (-17/320) (25/64) (1/320) tau := by
                convert childLR hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332331 | hx2332331
              · rcases le_total tau.im (25/64 : ℝ) with hy2332331 | hy2332331
                · have hs23323310 : InSquare (-7/128) (249/640) (1/640) tau := by
                    convert childLL hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3440.sound htau (by
                    simp only [Batch0430.cell3440, Batch0430.tau3440, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323310 (by positivity) using 1 <;> norm_num)
                · have hs23323312 : InSquare (-7/128) (251/640) (1/640) tau := by
                    convert childUL hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3442.sound htau (by
                    simp only [Batch0430.cell3442, Batch0430.tau3442, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332331 | hy2332331
                · have hs23323311 : InSquare (-33/640) (249/640) (1/640) tau := by
                    convert childLR hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3441.sound htau (by
                    simp only [Batch0430.cell3441, Batch0430.tau3441, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323311 (by positivity) using 1 <;> norm_num)
                · have hs23323313 : InSquare (-33/640) (251/640) (1/640) tau := by
                    convert childUR hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3443.sound htau (by
                    simp only [Batch0430.cell3443, Batch0430.tau3443, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323313 (by positivity) using 1 <;> norm_num)
            · have hs2332333 : InSquare (-17/320) (127/320) (1/320) tau := by
                convert childUR hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332333 | hx2332333
              · rcases le_total tau.im (127/320 : ℝ) with hy2332333 | hy2332333
                · have hs23323330 : InSquare (-7/128) (253/640) (1/640) tau := by
                    convert childLL hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact Batch0430.cell3446.sound htau (by
                    simp only [Batch0430.cell3446, Batch0430.tau3446, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323330 (by positivity) using 1 <;> norm_num)
                · have hs23323332 : InSquare (-7/128) (51/128) (1/640) tau := by
                    convert childUL hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact (outside_23323332 htau hs23323332).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332333 | hy2332333
                · have hs23323331 : InSquare (-33/640) (253/640) (1/640) tau := by
                    convert childLR hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact Batch0430.cell3447.sound htau (by
                    simp only [Batch0430.cell3447, Batch0430.tau3447, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323331 (by positivity) using 1 <;> norm_num)
                · have hs23323333 : InSquare (-33/640) (51/128) (1/640) tau := by
                    convert childUR hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact (outside_23323333 htau hs23323333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2333 | hx2333
  · rcases le_total tau.im (3/8 : ℝ) with hy2333 | hy2333
    · have hs23330 : InSquare (-3/80) (29/80) (1/80) tau := by
        convert childLL hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23330 | hx23330
      · rcases le_total tau.im (29/80 : ℝ) with hy23330 | hy23330
        · have hs233300 : InSquare (-7/160) (57/160) (1/160) tau := by
            convert childLL hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233300 | hx233300
          · rcases le_total tau.im (57/160 : ℝ) with hy233300 | hy233300
            · have hs2333000 : InSquare (-3/64) (113/320) (1/320) tau := by
                convert childLL hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0272.cell2182.sound htau (by
                simp only [Batch0272.cell2182, Batch0272.tau2182, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333000 (by positivity) using 1 <;> norm_num)
            · have hs2333002 : InSquare (-3/64) (23/64) (1/320) tau := by
                convert childUL hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0273.cell2184.sound htau (by
                simp only [Batch0273.cell2184, Batch0273.tau2184, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233300 | hy233300
            · have hs2333001 : InSquare (-13/320) (113/320) (1/320) tau := by
                convert childLR hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0272.cell2183.sound htau (by
                simp only [Batch0272.cell2183, Batch0272.tau2183, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333001 (by positivity) using 1 <;> norm_num)
            · have hs2333003 : InSquare (-13/320) (23/64) (1/320) tau := by
                convert childUR hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0273.cell2185.sound htau (by
                simp only [Batch0273.cell2185, Batch0273.tau2185, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333003 (by positivity) using 1 <;> norm_num)
        · have hs233302 : InSquare (-7/160) (59/160) (1/160) tau := by
            convert childUL hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233302 | hx233302
          · rcases le_total tau.im (59/160 : ℝ) with hy233302 | hy233302
            · have hs2333020 : InSquare (-3/64) (117/320) (1/320) tau := by
                convert childLL hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0273.cell2190.sound htau (by
                simp only [Batch0273.cell2190, Batch0273.tau2190, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333020 (by positivity) using 1 <;> norm_num)
            · have hs2333022 : InSquare (-3/64) (119/320) (1/320) tau := by
                convert childUL hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0274.cell2192.sound htau (by
                simp only [Batch0274.cell2192, Batch0274.tau2192, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233302 | hy233302
            · have hs2333021 : InSquare (-13/320) (117/320) (1/320) tau := by
                convert childLR hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0273.cell2191.sound htau (by
                simp only [Batch0273.cell2191, Batch0273.tau2191, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333021 (by positivity) using 1 <;> norm_num)
            · have hs2333023 : InSquare (-13/320) (119/320) (1/320) tau := by
                convert childUR hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0274.cell2193.sound htau (by
                simp only [Batch0274.cell2193, Batch0274.tau2193, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23330 | hy23330
        · have hs233301 : InSquare (-1/32) (57/160) (1/160) tau := by
            convert childLR hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233301 | hx233301
          · rcases le_total tau.im (57/160 : ℝ) with hy233301 | hy233301
            · have hs2333010 : InSquare (-11/320) (113/320) (1/320) tau := by
                convert childLL hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2186.sound htau (by
                simp only [Batch0273.cell2186, Batch0273.tau2186, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333010 (by positivity) using 1 <;> norm_num)
            · have hs2333012 : InSquare (-11/320) (23/64) (1/320) tau := by
                convert childUL hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2188.sound htau (by
                simp only [Batch0273.cell2188, Batch0273.tau2188, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233301 | hy233301
            · have hs2333011 : InSquare (-9/320) (113/320) (1/320) tau := by
                convert childLR hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2187.sound htau (by
                simp only [Batch0273.cell2187, Batch0273.tau2187, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333011 (by positivity) using 1 <;> norm_num)
            · have hs2333013 : InSquare (-9/320) (23/64) (1/320) tau := by
                convert childUR hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2189.sound htau (by
                simp only [Batch0273.cell2189, Batch0273.tau2189, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333013 (by positivity) using 1 <;> norm_num)
        · have hs233303 : InSquare (-1/32) (59/160) (1/160) tau := by
            convert childUR hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233303 | hx233303
          · rcases le_total tau.im (59/160 : ℝ) with hy233303 | hy233303
            · have hs2333030 : InSquare (-11/320) (117/320) (1/320) tau := by
                convert childLL hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2194.sound htau (by
                simp only [Batch0274.cell2194, Batch0274.tau2194, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333030 (by positivity) using 1 <;> norm_num)
            · have hs2333032 : InSquare (-11/320) (119/320) (1/320) tau := by
                convert childUL hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2196.sound htau (by
                simp only [Batch0274.cell2196, Batch0274.tau2196, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233303 | hy233303
            · have hs2333031 : InSquare (-9/320) (117/320) (1/320) tau := by
                convert childLR hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2195.sound htau (by
                simp only [Batch0274.cell2195, Batch0274.tau2195, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333031 (by positivity) using 1 <;> norm_num)
            · have hs2333033 : InSquare (-9/320) (119/320) (1/320) tau := by
                convert childUR hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2197.sound htau (by
                simp only [Batch0274.cell2197, Batch0274.tau2197, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333033 (by positivity) using 1 <;> norm_num)
    · have hs23332 : InSquare (-3/80) (31/80) (1/80) tau := by
        convert childUL hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23332 | hx23332
      · rcases le_total tau.im (31/80 : ℝ) with hy23332 | hy23332
        · have hs233320 : InSquare (-7/160) (61/160) (1/160) tau := by
            convert childLL hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233320 | hx233320
          · rcases le_total tau.im (61/160 : ℝ) with hy233320 | hy233320
            · have hs2333200 : InSquare (-3/64) (121/320) (1/320) tau := by
                convert childLL hs233320 hx233320 hy233320 using 1 <;> norm_num
              exact Batch0276.cell2210.sound htau (by
                simp only [Batch0276.cell2210, Batch0276.tau2210, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333200 (by positivity) using 1 <;> norm_num)
            · have hs2333202 : InSquare (-3/64) (123/320) (1/320) tau := by
                convert childUL hs233320 hx233320 hy233320 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333202 | hx2333202
              · rcases le_total tau.im (123/320 : ℝ) with hy2333202 | hy2333202
                · have hs23332020 : InSquare (-31/640) (49/128) (1/640) tau := by
                    convert childLL hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3448.sound htau (by
                    simp only [Batch0431.cell3448, Batch0431.tau3448, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332020 (by positivity) using 1 <;> norm_num)
                · have hs23332022 : InSquare (-31/640) (247/640) (1/640) tau := by
                    convert childUL hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3450.sound htau (by
                    simp only [Batch0431.cell3450, Batch0431.tau3450, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333202 | hy2333202
                · have hs23332021 : InSquare (-29/640) (49/128) (1/640) tau := by
                    convert childLR hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3449.sound htau (by
                    simp only [Batch0431.cell3449, Batch0431.tau3449, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332021 (by positivity) using 1 <;> norm_num)
                · have hs23332023 : InSquare (-29/640) (247/640) (1/640) tau := by
                    convert childUR hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3451.sound htau (by
                    simp only [Batch0431.cell3451, Batch0431.tau3451, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233320 | hy233320
            · have hs2333201 : InSquare (-13/320) (121/320) (1/320) tau := by
                convert childLR hs233320 hx233320 hy233320 using 1 <;> norm_num
              exact Batch0276.cell2211.sound htau (by
                simp only [Batch0276.cell2211, Batch0276.tau2211, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333201 (by positivity) using 1 <;> norm_num)
            · have hs2333203 : InSquare (-13/320) (123/320) (1/320) tau := by
                convert childUR hs233320 hx233320 hy233320 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333203 | hx2333203
              · rcases le_total tau.im (123/320 : ℝ) with hy2333203 | hy2333203
                · have hs23332030 : InSquare (-27/640) (49/128) (1/640) tau := by
                    convert childLL hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3452.sound htau (by
                    simp only [Batch0431.cell3452, Batch0431.tau3452, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332030 (by positivity) using 1 <;> norm_num)
                · have hs23332032 : InSquare (-27/640) (247/640) (1/640) tau := by
                    convert childUL hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3454.sound htau (by
                    simp only [Batch0431.cell3454, Batch0431.tau3454, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333203 | hy2333203
                · have hs23332031 : InSquare (-5/128) (49/128) (1/640) tau := by
                    convert childLR hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3453.sound htau (by
                    simp only [Batch0431.cell3453, Batch0431.tau3453, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332031 (by positivity) using 1 <;> norm_num)
                · have hs23332033 : InSquare (-5/128) (247/640) (1/640) tau := by
                    convert childUR hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3455.sound htau (by
                    simp only [Batch0431.cell3455, Batch0431.tau3455, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332033 (by positivity) using 1 <;> norm_num)
        · have hs233322 : InSquare (-7/160) (63/160) (1/160) tau := by
            convert childUL hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233322 | hx233322
          · rcases le_total tau.im (63/160 : ℝ) with hy233322 | hy233322
            · have hs2333220 : InSquare (-3/64) (25/64) (1/320) tau := by
                convert childLL hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333220 | hx2333220
              · rcases le_total tau.im (25/64 : ℝ) with hy2333220 | hy2333220
                · have hs23332200 : InSquare (-31/640) (249/640) (1/640) tau := by
                    convert childLL hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3460.sound htau (by
                    simp only [Batch0432.cell3460, Batch0432.tau3460, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332200 (by positivity) using 1 <;> norm_num)
                · have hs23332202 : InSquare (-31/640) (251/640) (1/640) tau := by
                    convert childUL hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3462.sound htau (by
                    simp only [Batch0432.cell3462, Batch0432.tau3462, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333220 | hy2333220
                · have hs23332201 : InSquare (-29/640) (249/640) (1/640) tau := by
                    convert childLR hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3461.sound htau (by
                    simp only [Batch0432.cell3461, Batch0432.tau3461, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332201 (by positivity) using 1 <;> norm_num)
                · have hs23332203 : InSquare (-29/640) (251/640) (1/640) tau := by
                    convert childUR hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3463.sound htau (by
                    simp only [Batch0432.cell3463, Batch0432.tau3463, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332203 (by positivity) using 1 <;> norm_num)
            · have hs2333222 : InSquare (-3/64) (127/320) (1/320) tau := by
                convert childUL hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333222 | hx2333222
              · rcases le_total tau.im (127/320 : ℝ) with hy2333222 | hy2333222
                · have hs23332220 : InSquare (-31/640) (253/640) (1/640) tau := by
                    convert childLL hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3468.sound htau (by
                    simp only [Batch0433.cell3468, Batch0433.tau3468, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332220 (by positivity) using 1 <;> norm_num)
                · have hs23332222 : InSquare (-31/640) (51/128) (1/640) tau := by
                    convert childUL hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3470.sound htau (by
                    simp only [Batch0433.cell3470, Batch0433.tau3470, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333222 | hy2333222
                · have hs23332221 : InSquare (-29/640) (253/640) (1/640) tau := by
                    convert childLR hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3469.sound htau (by
                    simp only [Batch0433.cell3469, Batch0433.tau3469, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332221 (by positivity) using 1 <;> norm_num)
                · have hs23332223 : InSquare (-29/640) (51/128) (1/640) tau := by
                    convert childUR hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3471.sound htau (by
                    simp only [Batch0433.cell3471, Batch0433.tau3471, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233322 | hy233322
            · have hs2333221 : InSquare (-13/320) (25/64) (1/320) tau := by
                convert childLR hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333221 | hx2333221
              · rcases le_total tau.im (25/64 : ℝ) with hy2333221 | hy2333221
                · have hs23332210 : InSquare (-27/640) (249/640) (1/640) tau := by
                    convert childLL hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3464.sound htau (by
                    simp only [Batch0433.cell3464, Batch0433.tau3464, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332210 (by positivity) using 1 <;> norm_num)
                · have hs23332212 : InSquare (-27/640) (251/640) (1/640) tau := by
                    convert childUL hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3466.sound htau (by
                    simp only [Batch0433.cell3466, Batch0433.tau3466, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333221 | hy2333221
                · have hs23332211 : InSquare (-5/128) (249/640) (1/640) tau := by
                    convert childLR hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3465.sound htau (by
                    simp only [Batch0433.cell3465, Batch0433.tau3465, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332211 (by positivity) using 1 <;> norm_num)
                · have hs23332213 : InSquare (-5/128) (251/640) (1/640) tau := by
                    convert childUR hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3467.sound htau (by
                    simp only [Batch0433.cell3467, Batch0433.tau3467, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332213 (by positivity) using 1 <;> norm_num)
            · have hs2333223 : InSquare (-13/320) (127/320) (1/320) tau := by
                convert childUR hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333223 | hx2333223
              · rcases le_total tau.im (127/320 : ℝ) with hy2333223 | hy2333223
                · have hs23332230 : InSquare (-27/640) (253/640) (1/640) tau := by
                    convert childLL hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3472.sound htau (by
                    simp only [Batch0434.cell3472, Batch0434.tau3472, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332230 (by positivity) using 1 <;> norm_num)
                · have hs23332232 : InSquare (-27/640) (51/128) (1/640) tau := by
                    convert childUL hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3474.sound htau (by
                    simp only [Batch0434.cell3474, Batch0434.tau3474, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333223 | hy2333223
                · have hs23332231 : InSquare (-5/128) (253/640) (1/640) tau := by
                    convert childLR hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3473.sound htau (by
                    simp only [Batch0434.cell3473, Batch0434.tau3473, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332231 (by positivity) using 1 <;> norm_num)
                · have hs23332233 : InSquare (-5/128) (51/128) (1/640) tau := by
                    convert childUR hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3475.sound htau (by
                    simp only [Batch0434.cell3475, Batch0434.tau3475, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy23332 | hy23332
        · have hs233321 : InSquare (-1/32) (61/160) (1/160) tau := by
            convert childLR hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233321 | hx233321
          · rcases le_total tau.im (61/160 : ℝ) with hy233321 | hy233321
            · have hs2333210 : InSquare (-11/320) (121/320) (1/320) tau := by
                convert childLL hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2212.sound htau (by
                simp only [Batch0276.cell2212, Batch0276.tau2212, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333210 (by positivity) using 1 <;> norm_num)
            · have hs2333212 : InSquare (-11/320) (123/320) (1/320) tau := by
                convert childUL hs233321 hx233321 hy233321 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333212 | hx2333212
              · rcases le_total tau.im (123/320 : ℝ) with hy2333212 | hy2333212
                · have hs23332120 : InSquare (-23/640) (49/128) (1/640) tau := by
                    convert childLL hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3456.sound htau (by
                    simp only [Batch0432.cell3456, Batch0432.tau3456, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332120 (by positivity) using 1 <;> norm_num)
                · have hs23332122 : InSquare (-23/640) (247/640) (1/640) tau := by
                    convert childUL hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3458.sound htau (by
                    simp only [Batch0432.cell3458, Batch0432.tau3458, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333212 | hy2333212
                · have hs23332121 : InSquare (-21/640) (49/128) (1/640) tau := by
                    convert childLR hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3457.sound htau (by
                    simp only [Batch0432.cell3457, Batch0432.tau3457, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332121 (by positivity) using 1 <;> norm_num)
                · have hs23332123 : InSquare (-21/640) (247/640) (1/640) tau := by
                    convert childUR hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3459.sound htau (by
                    simp only [Batch0432.cell3459, Batch0432.tau3459, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233321 | hy233321
            · have hs2333211 : InSquare (-9/320) (121/320) (1/320) tau := by
                convert childLR hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2213.sound htau (by
                simp only [Batch0276.cell2213, Batch0276.tau2213, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333211 (by positivity) using 1 <;> norm_num)
            · have hs2333213 : InSquare (-9/320) (123/320) (1/320) tau := by
                convert childUR hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2214.sound htau (by
                simp only [Batch0276.cell2214, Batch0276.tau2214, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333213 (by positivity) using 1 <;> norm_num)
        · have hs233323 : InSquare (-1/32) (63/160) (1/160) tau := by
            convert childUR hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233323 | hx233323
          · rcases le_total tau.im (63/160 : ℝ) with hy233323 | hy233323
            · have hs2333230 : InSquare (-11/320) (25/64) (1/320) tau := by
                convert childLL hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333230 | hx2333230
              · rcases le_total tau.im (25/64 : ℝ) with hy2333230 | hy2333230
                · have hs23332300 : InSquare (-23/640) (249/640) (1/640) tau := by
                    convert childLL hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3476.sound htau (by
                    simp only [Batch0434.cell3476, Batch0434.tau3476, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332300 (by positivity) using 1 <;> norm_num)
                · have hs23332302 : InSquare (-23/640) (251/640) (1/640) tau := by
                    convert childUL hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3478.sound htau (by
                    simp only [Batch0434.cell3478, Batch0434.tau3478, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333230 | hy2333230
                · have hs23332301 : InSquare (-21/640) (249/640) (1/640) tau := by
                    convert childLR hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3477.sound htau (by
                    simp only [Batch0434.cell3477, Batch0434.tau3477, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332301 (by positivity) using 1 <;> norm_num)
                · have hs23332303 : InSquare (-21/640) (251/640) (1/640) tau := by
                    convert childUR hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3479.sound htau (by
                    simp only [Batch0434.cell3479, Batch0434.tau3479, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332303 (by positivity) using 1 <;> norm_num)
            · have hs2333232 : InSquare (-11/320) (127/320) (1/320) tau := by
                convert childUL hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333232 | hx2333232
              · rcases le_total tau.im (127/320 : ℝ) with hy2333232 | hy2333232
                · have hs23332320 : InSquare (-23/640) (253/640) (1/640) tau := by
                    convert childLL hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3484.sound htau (by
                    simp only [Batch0435.cell3484, Batch0435.tau3484, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332320 (by positivity) using 1 <;> norm_num)
                · have hs23332322 : InSquare (-23/640) (51/128) (1/640) tau := by
                    convert childUL hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3486.sound htau (by
                    simp only [Batch0435.cell3486, Batch0435.tau3486, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333232 | hy2333232
                · have hs23332321 : InSquare (-21/640) (253/640) (1/640) tau := by
                    convert childLR hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3485.sound htau (by
                    simp only [Batch0435.cell3485, Batch0435.tau3485, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332321 (by positivity) using 1 <;> norm_num)
                · have hs23332323 : InSquare (-21/640) (51/128) (1/640) tau := by
                    convert childUR hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3487.sound htau (by
                    simp only [Batch0435.cell3487, Batch0435.tau3487, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233323 | hy233323
            · have hs2333231 : InSquare (-9/320) (25/64) (1/320) tau := by
                convert childLR hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx2333231 | hx2333231
              · rcases le_total tau.im (25/64 : ℝ) with hy2333231 | hy2333231
                · have hs23332310 : InSquare (-19/640) (249/640) (1/640) tau := by
                    convert childLL hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3480.sound htau (by
                    simp only [Batch0435.cell3480, Batch0435.tau3480, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332310 (by positivity) using 1 <;> norm_num)
                · have hs23332312 : InSquare (-19/640) (251/640) (1/640) tau := by
                    convert childUL hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3482.sound htau (by
                    simp only [Batch0435.cell3482, Batch0435.tau3482, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333231 | hy2333231
                · have hs23332311 : InSquare (-17/640) (249/640) (1/640) tau := by
                    convert childLR hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3481.sound htau (by
                    simp only [Batch0435.cell3481, Batch0435.tau3481, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332311 (by positivity) using 1 <;> norm_num)
                · have hs23332313 : InSquare (-17/640) (251/640) (1/640) tau := by
                    convert childUR hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3483.sound htau (by
                    simp only [Batch0435.cell3483, Batch0435.tau3483, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332313 (by positivity) using 1 <;> norm_num)
            · have hs2333233 : InSquare (-9/320) (127/320) (1/320) tau := by
                convert childUR hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx2333233 | hx2333233
              · rcases le_total tau.im (127/320 : ℝ) with hy2333233 | hy2333233
                · have hs23332330 : InSquare (-19/640) (253/640) (1/640) tau := by
                    convert childLL hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3488.sound htau (by
                    simp only [Batch0436.cell3488, Batch0436.tau3488, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332330 (by positivity) using 1 <;> norm_num)
                · have hs23332332 : InSquare (-19/640) (51/128) (1/640) tau := by
                    convert childUL hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3490.sound htau (by
                    simp only [Batch0436.cell3490, Batch0436.tau3490, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333233 | hy2333233
                · have hs23332331 : InSquare (-17/640) (253/640) (1/640) tau := by
                    convert childLR hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3489.sound htau (by
                    simp only [Batch0436.cell3489, Batch0436.tau3489, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332331 (by positivity) using 1 <;> norm_num)
                · have hs23332333 : InSquare (-17/640) (51/128) (1/640) tau := by
                    convert childUR hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3491.sound htau (by
                    simp only [Batch0436.cell3491, Batch0436.tau3491, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/8 : ℝ) with hy2333 | hy2333
    · have hs23331 : InSquare (-1/80) (29/80) (1/80) tau := by
        convert childLR hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23331 | hx23331
      · rcases le_total tau.im (29/80 : ℝ) with hy23331 | hy23331
        · have hs233310 : InSquare (-3/160) (57/160) (1/160) tau := by
            convert childLL hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233310 | hx233310
          · rcases le_total tau.im (57/160 : ℝ) with hy233310 | hy233310
            · have hs2333100 : InSquare (-7/320) (113/320) (1/320) tau := by
                convert childLL hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0274.cell2198.sound htau (by
                simp only [Batch0274.cell2198, Batch0274.tau2198, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333100 (by positivity) using 1 <;> norm_num)
            · have hs2333102 : InSquare (-7/320) (23/64) (1/320) tau := by
                convert childUL hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0275.cell2200.sound htau (by
                simp only [Batch0275.cell2200, Batch0275.tau2200, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233310 | hy233310
            · have hs2333101 : InSquare (-1/64) (113/320) (1/320) tau := by
                convert childLR hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0274.cell2199.sound htau (by
                simp only [Batch0274.cell2199, Batch0274.tau2199, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333101 (by positivity) using 1 <;> norm_num)
            · have hs2333103 : InSquare (-1/64) (23/64) (1/320) tau := by
                convert childUR hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0275.cell2201.sound htau (by
                simp only [Batch0275.cell2201, Batch0275.tau2201, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333103 (by positivity) using 1 <;> norm_num)
        · have hs233312 : InSquare (-3/160) (59/160) (1/160) tau := by
            convert childUL hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233312 | hx233312
          · rcases le_total tau.im (59/160 : ℝ) with hy233312 | hy233312
            · have hs2333120 : InSquare (-7/320) (117/320) (1/320) tau := by
                convert childLL hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2202.sound htau (by
                simp only [Batch0275.cell2202, Batch0275.tau2202, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333120 (by positivity) using 1 <;> norm_num)
            · have hs2333122 : InSquare (-7/320) (119/320) (1/320) tau := by
                convert childUL hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2204.sound htau (by
                simp only [Batch0275.cell2204, Batch0275.tau2204, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233312 | hy233312
            · have hs2333121 : InSquare (-1/64) (117/320) (1/320) tau := by
                convert childLR hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2203.sound htau (by
                simp only [Batch0275.cell2203, Batch0275.tau2203, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333121 (by positivity) using 1 <;> norm_num)
            · have hs2333123 : InSquare (-1/64) (119/320) (1/320) tau := by
                convert childUR hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2205.sound htau (by
                simp only [Batch0275.cell2205, Batch0275.tau2205, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23331 | hy23331
        · have hs233311 : InSquare (-1/160) (57/160) (1/160) tau := by
            convert childLR hs23331 hx23331 hy23331 using 1 <;> norm_num
          exact Batch0123.cell0985.sound htau (by
            simp only [Batch0123.cell0985, Batch0123.tau0985, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233311 (by positivity) using 1 <;> norm_num)
        · have hs233313 : InSquare (-1/160) (59/160) (1/160) tau := by
            convert childUR hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233313 | hx233313
          · rcases le_total tau.im (59/160 : ℝ) with hy233313 | hy233313
            · have hs2333130 : InSquare (-3/320) (117/320) (1/320) tau := by
                convert childLL hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0275.cell2206.sound htau (by
                simp only [Batch0275.cell2206, Batch0275.tau2206, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333130 (by positivity) using 1 <;> norm_num)
            · have hs2333132 : InSquare (-3/320) (119/320) (1/320) tau := by
                convert childUL hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0276.cell2208.sound htau (by
                simp only [Batch0276.cell2208, Batch0276.tau2208, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233313 | hy233313
            · have hs2333131 : InSquare (-1/320) (117/320) (1/320) tau := by
                convert childLR hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0275.cell2207.sound htau (by
                simp only [Batch0275.cell2207, Batch0275.tau2207, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333131 (by positivity) using 1 <;> norm_num)
            · have hs2333133 : InSquare (-1/320) (119/320) (1/320) tau := by
                convert childUR hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0276.cell2209.sound htau (by
                simp only [Batch0276.cell2209, Batch0276.tau2209, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333133 (by positivity) using 1 <;> norm_num)
    · have hs23333 : InSquare (-1/80) (31/80) (1/80) tau := by
        convert childUR hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23333 | hx23333
      · rcases le_total tau.im (31/80 : ℝ) with hy23333 | hy23333
        · have hs233330 : InSquare (-3/160) (61/160) (1/160) tau := by
            convert childLL hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233330 | hx233330
          · rcases le_total tau.im (61/160 : ℝ) with hy233330 | hy233330
            · have hs2333300 : InSquare (-7/320) (121/320) (1/320) tau := by
                convert childLL hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0276.cell2215.sound htau (by
                simp only [Batch0276.cell2215, Batch0276.tau2215, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333300 (by positivity) using 1 <;> norm_num)
            · have hs2333302 : InSquare (-7/320) (123/320) (1/320) tau := by
                convert childUL hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2217.sound htau (by
                simp only [Batch0277.cell2217, Batch0277.tau2217, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233330 | hy233330
            · have hs2333301 : InSquare (-1/64) (121/320) (1/320) tau := by
                convert childLR hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2216.sound htau (by
                simp only [Batch0277.cell2216, Batch0277.tau2216, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333301 (by positivity) using 1 <;> norm_num)
            · have hs2333303 : InSquare (-1/64) (123/320) (1/320) tau := by
                convert childUR hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2218.sound htau (by
                simp only [Batch0277.cell2218, Batch0277.tau2218, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333303 (by positivity) using 1 <;> norm_num)
        · have hs233332 : InSquare (-3/160) (63/160) (1/160) tau := by
            convert childUL hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233332 | hx233332
          · rcases le_total tau.im (63/160 : ℝ) with hy233332 | hy233332
            · have hs2333320 : InSquare (-7/320) (25/64) (1/320) tau := by
                convert childLL hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx2333320 | hx2333320
              · rcases le_total tau.im (25/64 : ℝ) with hy2333320 | hy2333320
                · have hs23333200 : InSquare (-3/128) (249/640) (1/640) tau := by
                    convert childLL hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3492.sound htau (by
                    simp only [Batch0436.cell3492, Batch0436.tau3492, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333200 (by positivity) using 1 <;> norm_num)
                · have hs23333202 : InSquare (-3/128) (251/640) (1/640) tau := by
                    convert childUL hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3494.sound htau (by
                    simp only [Batch0436.cell3494, Batch0436.tau3494, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333320 | hy2333320
                · have hs23333201 : InSquare (-13/640) (249/640) (1/640) tau := by
                    convert childLR hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3493.sound htau (by
                    simp only [Batch0436.cell3493, Batch0436.tau3493, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333201 (by positivity) using 1 <;> norm_num)
                · have hs23333203 : InSquare (-13/640) (251/640) (1/640) tau := by
                    convert childUR hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3495.sound htau (by
                    simp only [Batch0436.cell3495, Batch0436.tau3495, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333203 (by positivity) using 1 <;> norm_num)
            · have hs2333322 : InSquare (-7/320) (127/320) (1/320) tau := by
                convert childUL hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx2333322 | hx2333322
              · rcases le_total tau.im (127/320 : ℝ) with hy2333322 | hy2333322
                · have hs23333220 : InSquare (-3/128) (253/640) (1/640) tau := by
                    convert childLL hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3500.sound htau (by
                    simp only [Batch0437.cell3500, Batch0437.tau3500, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333220 (by positivity) using 1 <;> norm_num)
                · have hs23333222 : InSquare (-3/128) (51/128) (1/640) tau := by
                    convert childUL hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3502.sound htau (by
                    simp only [Batch0437.cell3502, Batch0437.tau3502, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333322 | hy2333322
                · have hs23333221 : InSquare (-13/640) (253/640) (1/640) tau := by
                    convert childLR hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3501.sound htau (by
                    simp only [Batch0437.cell3501, Batch0437.tau3501, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333221 (by positivity) using 1 <;> norm_num)
                · have hs23333223 : InSquare (-13/640) (51/128) (1/640) tau := by
                    convert childUR hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3503.sound htau (by
                    simp only [Batch0437.cell3503, Batch0437.tau3503, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233332 | hy233332
            · have hs2333321 : InSquare (-1/64) (25/64) (1/320) tau := by
                convert childLR hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx2333321 | hx2333321
              · rcases le_total tau.im (25/64 : ℝ) with hy2333321 | hy2333321
                · have hs23333210 : InSquare (-11/640) (249/640) (1/640) tau := by
                    convert childLL hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3496.sound htau (by
                    simp only [Batch0437.cell3496, Batch0437.tau3496, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333210 (by positivity) using 1 <;> norm_num)
                · have hs23333212 : InSquare (-11/640) (251/640) (1/640) tau := by
                    convert childUL hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3498.sound htau (by
                    simp only [Batch0437.cell3498, Batch0437.tau3498, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333321 | hy2333321
                · have hs23333211 : InSquare (-9/640) (249/640) (1/640) tau := by
                    convert childLR hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3497.sound htau (by
                    simp only [Batch0437.cell3497, Batch0437.tau3497, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333211 (by positivity) using 1 <;> norm_num)
                · have hs23333213 : InSquare (-9/640) (251/640) (1/640) tau := by
                    convert childUR hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3499.sound htau (by
                    simp only [Batch0437.cell3499, Batch0437.tau3499, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333213 (by positivity) using 1 <;> norm_num)
            · have hs2333323 : InSquare (-1/64) (127/320) (1/320) tau := by
                convert childUR hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx2333323 | hx2333323
              · rcases le_total tau.im (127/320 : ℝ) with hy2333323 | hy2333323
                · have hs23333230 : InSquare (-11/640) (253/640) (1/640) tau := by
                    convert childLL hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3504.sound htau (by
                    simp only [Batch0438.cell3504, Batch0438.tau3504, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333230 (by positivity) using 1 <;> norm_num)
                · have hs23333232 : InSquare (-11/640) (51/128) (1/640) tau := by
                    convert childUL hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3506.sound htau (by
                    simp only [Batch0438.cell3506, Batch0438.tau3506, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333323 | hy2333323
                · have hs23333231 : InSquare (-9/640) (253/640) (1/640) tau := by
                    convert childLR hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3505.sound htau (by
                    simp only [Batch0438.cell3505, Batch0438.tau3505, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333231 (by positivity) using 1 <;> norm_num)
                · have hs23333233 : InSquare (-9/640) (51/128) (1/640) tau := by
                    convert childUR hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3507.sound htau (by
                    simp only [Batch0438.cell3507, Batch0438.tau3507, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy23333 | hy23333
        · have hs233331 : InSquare (-1/160) (61/160) (1/160) tau := by
            convert childLR hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233331 | hx233331
          · rcases le_total tau.im (61/160 : ℝ) with hy233331 | hy233331
            · have hs2333310 : InSquare (-3/320) (121/320) (1/320) tau := by
                convert childLL hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2219.sound htau (by
                simp only [Batch0277.cell2219, Batch0277.tau2219, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333310 (by positivity) using 1 <;> norm_num)
            · have hs2333312 : InSquare (-3/320) (123/320) (1/320) tau := by
                convert childUL hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2221.sound htau (by
                simp only [Batch0277.cell2221, Batch0277.tau2221, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233331 | hy233331
            · have hs2333311 : InSquare (-1/320) (121/320) (1/320) tau := by
                convert childLR hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2220.sound htau (by
                simp only [Batch0277.cell2220, Batch0277.tau2220, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333311 (by positivity) using 1 <;> norm_num)
            · have hs2333313 : InSquare (-1/320) (123/320) (1/320) tau := by
                convert childUR hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2222.sound htau (by
                simp only [Batch0277.cell2222, Batch0277.tau2222, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333313 (by positivity) using 1 <;> norm_num)
        · have hs233333 : InSquare (-1/160) (63/160) (1/160) tau := by
            convert childUR hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233333 | hx233333
          · rcases le_total tau.im (63/160 : ℝ) with hy233333 | hy233333
            · have hs2333330 : InSquare (-3/320) (25/64) (1/320) tau := by
                convert childLL hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx2333330 | hx2333330
              · rcases le_total tau.im (25/64 : ℝ) with hy2333330 | hy2333330
                · have hs23333300 : InSquare (-7/640) (249/640) (1/640) tau := by
                    convert childLL hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3508.sound htau (by
                    simp only [Batch0438.cell3508, Batch0438.tau3508, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333300 (by positivity) using 1 <;> norm_num)
                · have hs23333302 : InSquare (-7/640) (251/640) (1/640) tau := by
                    convert childUL hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3510.sound htau (by
                    simp only [Batch0438.cell3510, Batch0438.tau3510, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333330 | hy2333330
                · have hs23333301 : InSquare (-1/128) (249/640) (1/640) tau := by
                    convert childLR hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3509.sound htau (by
                    simp only [Batch0438.cell3509, Batch0438.tau3509, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333301 (by positivity) using 1 <;> norm_num)
                · have hs23333303 : InSquare (-1/128) (251/640) (1/640) tau := by
                    convert childUR hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3511.sound htau (by
                    simp only [Batch0438.cell3511, Batch0438.tau3511, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333303 (by positivity) using 1 <;> norm_num)
            · have hs2333332 : InSquare (-3/320) (127/320) (1/320) tau := by
                convert childUL hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx2333332 | hx2333332
              · rcases le_total tau.im (127/320 : ℝ) with hy2333332 | hy2333332
                · have hs23333320 : InSquare (-7/640) (253/640) (1/640) tau := by
                    convert childLL hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3516.sound htau (by
                    simp only [Batch0439.cell3516, Batch0439.tau3516, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333320 (by positivity) using 1 <;> norm_num)
                · have hs23333322 : InSquare (-7/640) (51/128) (1/640) tau := by
                    convert childUL hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3518.sound htau (by
                    simp only [Batch0439.cell3518, Batch0439.tau3518, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333332 | hy2333332
                · have hs23333321 : InSquare (-1/128) (253/640) (1/640) tau := by
                    convert childLR hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3517.sound htau (by
                    simp only [Batch0439.cell3517, Batch0439.tau3517, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333321 (by positivity) using 1 <;> norm_num)
                · have hs23333323 : InSquare (-1/128) (51/128) (1/640) tau := by
                    convert childUR hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3519.sound htau (by
                    simp only [Batch0439.cell3519, Batch0439.tau3519, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233333 | hy233333
            · have hs2333331 : InSquare (-1/320) (25/64) (1/320) tau := by
                convert childLR hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx2333331 | hx2333331
              · rcases le_total tau.im (25/64 : ℝ) with hy2333331 | hy2333331
                · have hs23333310 : InSquare (-3/640) (249/640) (1/640) tau := by
                    convert childLL hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3512.sound htau (by
                    simp only [Batch0439.cell3512, Batch0439.tau3512, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333310 (by positivity) using 1 <;> norm_num)
                · have hs23333312 : InSquare (-3/640) (251/640) (1/640) tau := by
                    convert childUL hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3514.sound htau (by
                    simp only [Batch0439.cell3514, Batch0439.tau3514, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333331 | hy2333331
                · have hs23333311 : InSquare (-1/640) (249/640) (1/640) tau := by
                    convert childLR hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3513.sound htau (by
                    simp only [Batch0439.cell3513, Batch0439.tau3513, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333311 (by positivity) using 1 <;> norm_num)
                · have hs23333313 : InSquare (-1/640) (251/640) (1/640) tau := by
                    convert childUR hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3515.sound htau (by
                    simp only [Batch0439.cell3515, Batch0439.tau3515, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333313 (by positivity) using 1 <;> norm_num)
            · have hs2333333 : InSquare (-1/320) (127/320) (1/320) tau := by
                convert childUR hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx2333333 | hx2333333
              · rcases le_total tau.im (127/320 : ℝ) with hy2333333 | hy2333333
                · have hs23333330 : InSquare (-3/640) (253/640) (1/640) tau := by
                    convert childLL hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3520.sound htau (by
                    simp only [Batch0440.cell3520, Batch0440.tau3520, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333330 (by positivity) using 1 <;> norm_num)
                · have hs23333332 : InSquare (-3/640) (51/128) (1/640) tau := by
                    convert childUL hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3522.sound htau (by
                    simp only [Batch0440.cell3522, Batch0440.tau3522, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333333 | hy2333333
                · have hs23333331 : InSquare (-1/640) (253/640) (1/640) tau := by
                    convert childLR hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3521.sound htau (by
                    simp only [Batch0440.cell3521, Batch0440.tau3521, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333331 (by positivity) using 1 <;> norm_num)
                · have hs23333333 : InSquare (-1/640) (51/128) (1/640) tau := by
                    convert childUR hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3523.sound htau (by
                    simp only [Batch0440.cell3523, Batch0440.tau3523, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3023 | hx3023
  · rcases le_total tau.im (7/40 : ℝ) with hy3023 | hy3023
    · have hs30230 : InSquare (1/16) (13/80) (1/80) tau := by
        convert childLL hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0033.cell0271.sound htau (by
        simp only [Batch0033.cell0271, Batch0033.tau0271, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30230 (by positivity) using 1 <;> norm_num)
    · have hs30232 : InSquare (1/16) (3/16) (1/80) tau := by
        convert childUL hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0273.sound htau (by
        simp only [Batch0034.cell0273, Batch0034.tau0273, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3023 | hy3023
    · have hs30231 : InSquare (7/80) (13/80) (1/80) tau := by
        convert childLR hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0272.sound htau (by
        simp only [Batch0034.cell0272, Batch0034.tau0272, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30231 (by positivity) using 1 <;> norm_num)
    · have hs30233 : InSquare (7/80) (3/16) (1/80) tau := by
        convert childUR hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0274.sound htau (by
        simp only [Batch0034.cell0274, Batch0034.tau0274, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3031 | hx3031
  · rcases le_total tau.im (1/8 : ℝ) with hy3031 | hy3031
    · have hs30310 : InSquare (13/80) (9/80) (1/80) tau := by
        convert childLL hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0275.sound htau (by
        simp only [Batch0034.cell0275, Batch0034.tau0275, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30310 (by positivity) using 1 <;> norm_num)
    · have hs30312 : InSquare (13/80) (11/80) (1/80) tau := by
        convert childUL hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0277.sound htau (by
        simp only [Batch0034.cell0277, Batch0034.tau0277, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3031 | hy3031
    · have hs30311 : InSquare (3/16) (9/80) (1/80) tau := by
        convert childLR hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0276.sound htau (by
        simp only [Batch0034.cell0276, Batch0034.tau0276, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30311 (by positivity) using 1 <;> norm_num)
    · have hs30313 : InSquare (3/16) (11/80) (1/80) tau := by
        convert childUR hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0278.sound htau (by
        simp only [Batch0034.cell0278, Batch0034.tau0278, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3032 | hx3032
  · rcases le_total tau.im (7/40 : ℝ) with hy3032 | hy3032
    · have hs30320 : InSquare (9/80) (13/80) (1/80) tau := by
        convert childLL hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0034.cell0279.sound htau (by
        simp only [Batch0034.cell0279, Batch0034.tau0279, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30320 (by positivity) using 1 <;> norm_num)
    · have hs30322 : InSquare (9/80) (3/16) (1/80) tau := by
        convert childUL hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0281.sound htau (by
        simp only [Batch0035.cell0281, Batch0035.tau0281, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3032 | hy3032
    · have hs30321 : InSquare (11/80) (13/80) (1/80) tau := by
        convert childLR hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0280.sound htau (by
        simp only [Batch0035.cell0280, Batch0035.tau0280, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30321 (by positivity) using 1 <;> norm_num)
    · have hs30323 : InSquare (11/80) (3/16) (1/80) tau := by
        convert childUR hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0282.sound htau (by
        simp only [Batch0035.cell0282, Batch0035.tau0282, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3033 | hx3033
  · rcases le_total tau.im (7/40 : ℝ) with hy3033 | hy3033
    · have hs30330 : InSquare (13/80) (13/80) (1/80) tau := by
        convert childLL hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0283.sound htau (by
        simp only [Batch0035.cell0283, Batch0035.tau0283, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30330 (by positivity) using 1 <;> norm_num)
    · have hs30332 : InSquare (13/80) (3/16) (1/80) tau := by
        convert childUL hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0285.sound htau (by
        simp only [Batch0035.cell0285, Batch0035.tau0285, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3033 | hy3033
    · have hs30331 : InSquare (3/16) (13/80) (1/80) tau := by
        convert childLR hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0284.sound htau (by
        simp only [Batch0035.cell0284, Batch0035.tau0284, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30331 (by positivity) using 1 <;> norm_num)
    · have hs30333 : InSquare (3/16) (3/16) (1/80) tau := by
        convert childUR hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0286.sound htau (by
        simp only [Batch0035.cell0286, Batch0035.tau0286, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3101 | hx3101
  · rcases le_total tau.im (1/40 : ℝ) with hy3101 | hy3101
    · have hs31010 : InSquare (21/80) (1/80) (1/80) tau := by
        convert childLL hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0035.cell0287.sound htau (by
        simp only [Batch0035.cell0287, Batch0035.tau0287, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31010 (by positivity) using 1 <;> norm_num)
    · have hs31012 : InSquare (21/80) (3/80) (1/80) tau := by
        convert childUL hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0289.sound htau (by
        simp only [Batch0036.cell0289, Batch0036.tau0289, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3101 | hy3101
    · have hs31011 : InSquare (23/80) (1/80) (1/80) tau := by
        convert childLR hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0288.sound htau (by
        simp only [Batch0036.cell0288, Batch0036.tau0288, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31011 (by positivity) using 1 <;> norm_num)
    · have hs31013 : InSquare (23/80) (3/80) (1/80) tau := by
        convert childUR hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0290.sound htau (by
        simp only [Batch0036.cell0290, Batch0036.tau0290, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3102 | hx3102
  · rcases le_total tau.im (3/40 : ℝ) with hy3102 | hy3102
    · have hs31020 : InSquare (17/80) (1/16) (1/80) tau := by
        convert childLL hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0291.sound htau (by
        simp only [Batch0036.cell0291, Batch0036.tau0291, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31020 (by positivity) using 1 <;> norm_num)
    · have hs31022 : InSquare (17/80) (7/80) (1/80) tau := by
        convert childUL hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0293.sound htau (by
        simp only [Batch0036.cell0293, Batch0036.tau0293, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3102 | hy3102
    · have hs31021 : InSquare (19/80) (1/16) (1/80) tau := by
        convert childLR hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0292.sound htau (by
        simp only [Batch0036.cell0292, Batch0036.tau0292, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31021 (by positivity) using 1 <;> norm_num)
    · have hs31023 : InSquare (19/80) (7/80) (1/80) tau := by
        convert childUR hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0294.sound htau (by
        simp only [Batch0036.cell0294, Batch0036.tau0294, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102

end


