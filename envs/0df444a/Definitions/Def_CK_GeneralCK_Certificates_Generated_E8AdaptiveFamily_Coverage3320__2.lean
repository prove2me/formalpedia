-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3320__2
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3320__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:23:43.663038+00:00
-- url     : https://prove2.me/theorems/3d1a6407-7320-4bda-8e95-b2b79807b46f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320 (+1 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320 (+1 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320 (+1 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320 (+1 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3320 (+1 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3321).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0316
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0317
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0319
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0479
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0480
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0320

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_332031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/320) (103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (67/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (69/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/320) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3320303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/64) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (143/640) (43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (129/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (131/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (137/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33202303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33203011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33203012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (149/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33203013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3320 | hx3320
  · rcases le_total tau.im (13/40 : ℝ) with hy3320 | hy3320
    · have hs33200 : InSquare (17/80) (5/16) (1/80) tau := by
        convert childLL hs hx3320 hy3320 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33200 | hx33200
      · rcases le_total tau.im (5/16 : ℝ) with hy33200 | hy33200
        · have hs332000 : InSquare (33/160) (49/160) (1/160) tau := by
            convert childLL hs33200 hx33200 hy33200 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx332000 | hx332000
          · rcases le_total tau.im (49/160 : ℝ) with hy332000 | hy332000
            · have hs3320000 : InSquare (13/64) (97/320) (1/320) tau := by
                convert childLL hs332000 hx332000 hy332000 using 1 <;> norm_num
              exact Batch0315.cell2520.sound htau (by
                simp only [Batch0315.cell2520, Batch0315.tau2520, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320000 (by positivity) using 1 <;> norm_num)
            · have hs3320002 : InSquare (13/64) (99/320) (1/320) tau := by
                convert childUL hs332000 hx332000 hy332000 using 1 <;> norm_num
              exact Batch0315.cell2522.sound htau (by
                simp only [Batch0315.cell2522, Batch0315.tau2522, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332000 | hy332000
            · have hs3320001 : InSquare (67/320) (97/320) (1/320) tau := by
                convert childLR hs332000 hx332000 hy332000 using 1 <;> norm_num
              exact Batch0315.cell2521.sound htau (by
                simp only [Batch0315.cell2521, Batch0315.tau2521, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320001 (by positivity) using 1 <;> norm_num)
            · have hs3320003 : InSquare (67/320) (99/320) (1/320) tau := by
                convert childUR hs332000 hx332000 hy332000 using 1 <;> norm_num
              exact Batch0315.cell2523.sound htau (by
                simp only [Batch0315.cell2523, Batch0315.tau2523, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320003 (by positivity) using 1 <;> norm_num)
        · have hs332002 : InSquare (33/160) (51/160) (1/160) tau := by
            convert childUL hs33200 hx33200 hy33200 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx332002 | hx332002
          · rcases le_total tau.im (51/160 : ℝ) with hy332002 | hy332002
            · have hs3320020 : InSquare (13/64) (101/320) (1/320) tau := by
                convert childLL hs332002 hx332002 hy332002 using 1 <;> norm_num
              exact Batch0316.cell2528.sound htau (by
                simp only [Batch0316.cell2528, Batch0316.tau2528, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320020 (by positivity) using 1 <;> norm_num)
            · have hs3320022 : InSquare (13/64) (103/320) (1/320) tau := by
                convert childUL hs332002 hx332002 hy332002 using 1 <;> norm_num
              exact Batch0316.cell2530.sound htau (by
                simp only [Batch0316.cell2530, Batch0316.tau2530, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy332002 | hy332002
            · have hs3320021 : InSquare (67/320) (101/320) (1/320) tau := by
                convert childLR hs332002 hx332002 hy332002 using 1 <;> norm_num
              exact Batch0316.cell2529.sound htau (by
                simp only [Batch0316.cell2529, Batch0316.tau2529, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320021 (by positivity) using 1 <;> norm_num)
            · have hs3320023 : InSquare (67/320) (103/320) (1/320) tau := by
                convert childUR hs332002 hx332002 hy332002 using 1 <;> norm_num
              exact Batch0316.cell2531.sound htau (by
                simp only [Batch0316.cell2531, Batch0316.tau2531, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy33200 | hy33200
        · have hs332001 : InSquare (7/32) (49/160) (1/160) tau := by
            convert childLR hs33200 hx33200 hy33200 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx332001 | hx332001
          · rcases le_total tau.im (49/160 : ℝ) with hy332001 | hy332001
            · have hs3320010 : InSquare (69/320) (97/320) (1/320) tau := by
                convert childLL hs332001 hx332001 hy332001 using 1 <;> norm_num
              exact Batch0315.cell2524.sound htau (by
                simp only [Batch0315.cell2524, Batch0315.tau2524, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320010 (by positivity) using 1 <;> norm_num)
            · have hs3320012 : InSquare (69/320) (99/320) (1/320) tau := by
                convert childUL hs332001 hx332001 hy332001 using 1 <;> norm_num
              exact Batch0315.cell2526.sound htau (by
                simp only [Batch0315.cell2526, Batch0315.tau2526, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332001 | hy332001
            · have hs3320011 : InSquare (71/320) (97/320) (1/320) tau := by
                convert childLR hs332001 hx332001 hy332001 using 1 <;> norm_num
              exact Batch0315.cell2525.sound htau (by
                simp only [Batch0315.cell2525, Batch0315.tau2525, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320011 (by positivity) using 1 <;> norm_num)
            · have hs3320013 : InSquare (71/320) (99/320) (1/320) tau := by
                convert childUR hs332001 hx332001 hy332001 using 1 <;> norm_num
              exact Batch0315.cell2527.sound htau (by
                simp only [Batch0315.cell2527, Batch0315.tau2527, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320013 (by positivity) using 1 <;> norm_num)
        · have hs332003 : InSquare (7/32) (51/160) (1/160) tau := by
            convert childUR hs33200 hx33200 hy33200 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx332003 | hx332003
          · rcases le_total tau.im (51/160 : ℝ) with hy332003 | hy332003
            · have hs3320030 : InSquare (69/320) (101/320) (1/320) tau := by
                convert childLL hs332003 hx332003 hy332003 using 1 <;> norm_num
              exact Batch0316.cell2532.sound htau (by
                simp only [Batch0316.cell2532, Batch0316.tau2532, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320030 (by positivity) using 1 <;> norm_num)
            · have hs3320032 : InSquare (69/320) (103/320) (1/320) tau := by
                convert childUL hs332003 hx332003 hy332003 using 1 <;> norm_num
              exact Batch0316.cell2534.sound htau (by
                simp only [Batch0316.cell2534, Batch0316.tau2534, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy332003 | hy332003
            · have hs3320031 : InSquare (71/320) (101/320) (1/320) tau := by
                convert childLR hs332003 hx332003 hy332003 using 1 <;> norm_num
              exact Batch0316.cell2533.sound htau (by
                simp only [Batch0316.cell2533, Batch0316.tau2533, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320031 (by positivity) using 1 <;> norm_num)
            · have hs3320033 : InSquare (71/320) (103/320) (1/320) tau := by
                convert childUR hs332003 hx332003 hy332003 using 1 <;> norm_num
              exact Batch0316.cell2535.sound htau (by
                simp only [Batch0316.cell2535, Batch0316.tau2535, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320033 (by positivity) using 1 <;> norm_num)
    · have hs33202 : InSquare (17/80) (27/80) (1/80) tau := by
        convert childUL hs hx3320 hy3320 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33202 | hx33202
      · rcases le_total tau.im (27/80 : ℝ) with hy33202 | hy33202
        · have hs332020 : InSquare (33/160) (53/160) (1/160) tau := by
            convert childLL hs33202 hx33202 hy33202 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx332020 | hx332020
          · rcases le_total tau.im (53/160 : ℝ) with hy332020 | hy332020
            · have hs3320200 : InSquare (13/64) (21/64) (1/320) tau := by
                convert childLL hs332020 hx332020 hy332020 using 1 <;> norm_num
              exact Batch0318.cell2551.sound htau (by
                simp only [Batch0318.cell2551, Batch0318.tau2551, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320200 (by positivity) using 1 <;> norm_num)
            · have hs3320202 : InSquare (13/64) (107/320) (1/320) tau := by
                convert childUL hs332020 hx332020 hy332020 using 1 <;> norm_num
              exact Batch0319.cell2553.sound htau (by
                simp only [Batch0319.cell2553, Batch0319.tau2553, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy332020 | hy332020
            · have hs3320201 : InSquare (67/320) (21/64) (1/320) tau := by
                convert childLR hs332020 hx332020 hy332020 using 1 <;> norm_num
              exact Batch0319.cell2552.sound htau (by
                simp only [Batch0319.cell2552, Batch0319.tau2552, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320201 (by positivity) using 1 <;> norm_num)
            · have hs3320203 : InSquare (67/320) (107/320) (1/320) tau := by
                convert childUR hs332020 hx332020 hy332020 using 1 <;> norm_num
              exact Batch0319.cell2554.sound htau (by
                simp only [Batch0319.cell2554, Batch0319.tau2554, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320203 (by positivity) using 1 <;> norm_num)
        · have hs332022 : InSquare (33/160) (11/32) (1/160) tau := by
            convert childUL hs33202 hx33202 hy33202 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx332022 | hx332022
          · rcases le_total tau.im (11/32 : ℝ) with hy332022 | hy332022
            · have hs3320220 : InSquare (13/64) (109/320) (1/320) tau := by
                convert childLL hs332022 hx332022 hy332022 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx3320220 | hx3320220
              · rcases le_total tau.im (109/320 : ℝ) with hy3320220 | hy3320220
                · have hs33202200 : InSquare (129/640) (217/640) (1/640) tau := by
                    convert childLL hs3320220 hx3320220 hy3320220 using 1 <;> norm_num
                  exact Batch0479.cell3832.sound htau (by
                    simp only [Batch0479.cell3832, Batch0479.tau3832, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202200 (by positivity) using 1 <;> norm_num)
                · have hs33202202 : InSquare (129/640) (219/640) (1/640) tau := by
                    convert childUL hs3320220 hx3320220 hy3320220 using 1 <;> norm_num
                  exact Batch0479.cell3834.sound htau (by
                    simp only [Batch0479.cell3834, Batch0479.tau3834, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy3320220 | hy3320220
                · have hs33202201 : InSquare (131/640) (217/640) (1/640) tau := by
                    convert childLR hs3320220 hx3320220 hy3320220 using 1 <;> norm_num
                  exact Batch0479.cell3833.sound htau (by
                    simp only [Batch0479.cell3833, Batch0479.tau3833, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202201 (by positivity) using 1 <;> norm_num)
                · have hs33202203 : InSquare (131/640) (219/640) (1/640) tau := by
                    convert childUR hs3320220 hx3320220 hy3320220 using 1 <;> norm_num
                  exact Batch0479.cell3835.sound htau (by
                    simp only [Batch0479.cell3835, Batch0479.tau3835, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202203 (by positivity) using 1 <;> norm_num)
            · have hs3320222 : InSquare (13/64) (111/320) (1/320) tau := by
                convert childUL hs332022 hx332022 hy332022 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx3320222 | hx3320222
              · rcases le_total tau.im (111/320 : ℝ) with hy3320222 | hy3320222
                · have hs33202220 : InSquare (129/640) (221/640) (1/640) tau := by
                    convert childLL hs3320222 hx3320222 hy3320222 using 1 <;> norm_num
                  exact Batch0480.cell3840.sound htau (by
                    simp only [Batch0480.cell3840, Batch0480.tau3840, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202220 (by positivity) using 1 <;> norm_num)
                · have hs33202222 : InSquare (129/640) (223/640) (1/640) tau := by
                    convert childUL hs3320222 hx3320222 hy3320222 using 1 <;> norm_num
                  exact (outside_33202222 htau hs33202222).elim
              · rcases le_total tau.im (111/320 : ℝ) with hy3320222 | hy3320222
                · have hs33202221 : InSquare (131/640) (221/640) (1/640) tau := by
                    convert childLR hs3320222 hx3320222 hy3320222 using 1 <;> norm_num
                  exact Batch0480.cell3841.sound htau (by
                    simp only [Batch0480.cell3841, Batch0480.tau3841, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202221 (by positivity) using 1 <;> norm_num)
                · have hs33202223 : InSquare (131/640) (223/640) (1/640) tau := by
                    convert childUR hs3320222 hx3320222 hy3320222 using 1 <;> norm_num
                  exact (outside_33202223 htau hs33202223).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy332022 | hy332022
            · have hs3320221 : InSquare (67/320) (109/320) (1/320) tau := by
                convert childLR hs332022 hx332022 hy332022 using 1 <;> norm_num
              rcases le_total tau.re (67/320 : ℝ) with hx3320221 | hx3320221
              · rcases le_total tau.im (109/320 : ℝ) with hy3320221 | hy3320221
                · have hs33202210 : InSquare (133/640) (217/640) (1/640) tau := by
                    convert childLL hs3320221 hx3320221 hy3320221 using 1 <;> norm_num
                  exact Batch0479.cell3836.sound htau (by
                    simp only [Batch0479.cell3836, Batch0479.tau3836, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202210 (by positivity) using 1 <;> norm_num)
                · have hs33202212 : InSquare (133/640) (219/640) (1/640) tau := by
                    convert childUL hs3320221 hx3320221 hy3320221 using 1 <;> norm_num
                  exact Batch0479.cell3838.sound htau (by
                    simp only [Batch0479.cell3838, Batch0479.tau3838, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy3320221 | hy3320221
                · have hs33202211 : InSquare (27/128) (217/640) (1/640) tau := by
                    convert childLR hs3320221 hx3320221 hy3320221 using 1 <;> norm_num
                  exact Batch0479.cell3837.sound htau (by
                    simp only [Batch0479.cell3837, Batch0479.tau3837, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202211 (by positivity) using 1 <;> norm_num)
                · have hs33202213 : InSquare (27/128) (219/640) (1/640) tau := by
                    convert childUR hs3320221 hx3320221 hy3320221 using 1 <;> norm_num
                  exact Batch0479.cell3839.sound htau (by
                    simp only [Batch0479.cell3839, Batch0479.tau3839, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202213 (by positivity) using 1 <;> norm_num)
            · have hs3320223 : InSquare (67/320) (111/320) (1/320) tau := by
                convert childUR hs332022 hx332022 hy332022 using 1 <;> norm_num
              exact (outside_3320223 htau hs3320223).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy33202 | hy33202
        · have hs332021 : InSquare (7/32) (53/160) (1/160) tau := by
            convert childLR hs33202 hx33202 hy33202 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx332021 | hx332021
          · rcases le_total tau.im (53/160 : ℝ) with hy332021 | hy332021
            · have hs3320210 : InSquare (69/320) (21/64) (1/320) tau := by
                convert childLL hs332021 hx332021 hy332021 using 1 <;> norm_num
              exact Batch0319.cell2555.sound htau (by
                simp only [Batch0319.cell2555, Batch0319.tau2555, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320210 (by positivity) using 1 <;> norm_num)
            · have hs3320212 : InSquare (69/320) (107/320) (1/320) tau := by
                convert childUL hs332021 hx332021 hy332021 using 1 <;> norm_num
              exact Batch0319.cell2557.sound htau (by
                simp only [Batch0319.cell2557, Batch0319.tau2557, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy332021 | hy332021
            · have hs3320211 : InSquare (71/320) (21/64) (1/320) tau := by
                convert childLR hs332021 hx332021 hy332021 using 1 <;> norm_num
              exact Batch0319.cell2556.sound htau (by
                simp only [Batch0319.cell2556, Batch0319.tau2556, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320211 (by positivity) using 1 <;> norm_num)
            · have hs3320213 : InSquare (71/320) (107/320) (1/320) tau := by
                convert childUR hs332021 hx332021 hy332021 using 1 <;> norm_num
              rcases le_total tau.re (71/320 : ℝ) with hx3320213 | hx3320213
              · rcases le_total tau.im (107/320 : ℝ) with hy3320213 | hy3320213
                · have hs33202130 : InSquare (141/640) (213/640) (1/640) tau := by
                    convert childLL hs3320213 hx3320213 hy3320213 using 1 <;> norm_num
                  exact Batch0478.cell3829.sound htau (by
                    simp only [Batch0478.cell3829, Batch0478.tau3829, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202130 (by positivity) using 1 <;> norm_num)
                · have hs33202132 : InSquare (141/640) (43/128) (1/640) tau := by
                    convert childUL hs3320213 hx3320213 hy3320213 using 1 <;> norm_num
                  exact Batch0478.cell3831.sound htau (by
                    simp only [Batch0478.cell3831, Batch0478.tau3831, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (107/320 : ℝ) with hy3320213 | hy3320213
                · have hs33202131 : InSquare (143/640) (213/640) (1/640) tau := by
                    convert childLR hs3320213 hx3320213 hy3320213 using 1 <;> norm_num
                  exact Batch0478.cell3830.sound htau (by
                    simp only [Batch0478.cell3830, Batch0478.tau3830, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202131 (by positivity) using 1 <;> norm_num)
                · have hs33202133 : InSquare (143/640) (43/128) (1/640) tau := by
                    convert childUR hs3320213 hx3320213 hy3320213 using 1 <;> norm_num
                  exact (outside_33202133 htau hs33202133).elim
        · have hs332023 : InSquare (7/32) (11/32) (1/160) tau := by
            convert childUR hs33202 hx33202 hy33202 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx332023 | hx332023
          · rcases le_total tau.im (11/32 : ℝ) with hy332023 | hy332023
            · have hs3320230 : InSquare (69/320) (109/320) (1/320) tau := by
                convert childLL hs332023 hx332023 hy332023 using 1 <;> norm_num
              rcases le_total tau.re (69/320 : ℝ) with hx3320230 | hx3320230
              · rcases le_total tau.im (109/320 : ℝ) with hy3320230 | hy3320230
                · have hs33202300 : InSquare (137/640) (217/640) (1/640) tau := by
                    convert childLL hs3320230 hx3320230 hy3320230 using 1 <;> norm_num
                  exact Batch0480.cell3842.sound htau (by
                    simp only [Batch0480.cell3842, Batch0480.tau3842, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33202300 (by positivity) using 1 <;> norm_num)
                · have hs33202302 : InSquare (137/640) (219/640) (1/640) tau := by
                    convert childUL hs3320230 hx3320230 hy3320230 using 1 <;> norm_num
                  exact (outside_33202302 htau hs33202302).elim
              · rcases le_total tau.im (109/320 : ℝ) with hy3320230 | hy3320230
                · have hs33202301 : InSquare (139/640) (217/640) (1/640) tau := by
                    convert childLR hs3320230 hx3320230 hy3320230 using 1 <;> norm_num
                  exact (outside_33202301 htau hs33202301).elim
                · have hs33202303 : InSquare (139/640) (219/640) (1/640) tau := by
                    convert childUR hs3320230 hx3320230 hy3320230 using 1 <;> norm_num
                  exact (outside_33202303 htau hs33202303).elim
            · have hs3320232 : InSquare (69/320) (111/320) (1/320) tau := by
                convert childUL hs332023 hx332023 hy332023 using 1 <;> norm_num
              exact (outside_3320232 htau hs3320232).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy332023 | hy332023
            · have hs3320231 : InSquare (71/320) (109/320) (1/320) tau := by
                convert childLR hs332023 hx332023 hy332023 using 1 <;> norm_num
              exact (outside_3320231 htau hs3320231).elim
            · have hs3320233 : InSquare (71/320) (111/320) (1/320) tau := by
                convert childUR hs332023 hx332023 hy332023 using 1 <;> norm_num
              exact (outside_3320233 htau hs3320233).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy3320 | hy3320
    · have hs33201 : InSquare (19/80) (5/16) (1/80) tau := by
        convert childLR hs hx3320 hy3320 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33201 | hx33201
      · rcases le_total tau.im (5/16 : ℝ) with hy33201 | hy33201
        · have hs332010 : InSquare (37/160) (49/160) (1/160) tau := by
            convert childLL hs33201 hx33201 hy33201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx332010 | hx332010
          · rcases le_total tau.im (49/160 : ℝ) with hy332010 | hy332010
            · have hs3320100 : InSquare (73/320) (97/320) (1/320) tau := by
                convert childLL hs332010 hx332010 hy332010 using 1 <;> norm_num
              exact Batch0317.cell2536.sound htau (by
                simp only [Batch0317.cell2536, Batch0317.tau2536, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320100 (by positivity) using 1 <;> norm_num)
            · have hs3320102 : InSquare (73/320) (99/320) (1/320) tau := by
                convert childUL hs332010 hx332010 hy332010 using 1 <;> norm_num
              exact Batch0317.cell2538.sound htau (by
                simp only [Batch0317.cell2538, Batch0317.tau2538, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332010 | hy332010
            · have hs3320101 : InSquare (15/64) (97/320) (1/320) tau := by
                convert childLR hs332010 hx332010 hy332010 using 1 <;> norm_num
              exact Batch0317.cell2537.sound htau (by
                simp only [Batch0317.cell2537, Batch0317.tau2537, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320101 (by positivity) using 1 <;> norm_num)
            · have hs3320103 : InSquare (15/64) (99/320) (1/320) tau := by
                convert childUR hs332010 hx332010 hy332010 using 1 <;> norm_num
              exact Batch0317.cell2539.sound htau (by
                simp only [Batch0317.cell2539, Batch0317.tau2539, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320103 (by positivity) using 1 <;> norm_num)
        · have hs332012 : InSquare (37/160) (51/160) (1/160) tau := by
            convert childUL hs33201 hx33201 hy33201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx332012 | hx332012
          · rcases le_total tau.im (51/160 : ℝ) with hy332012 | hy332012
            · have hs3320120 : InSquare (73/320) (101/320) (1/320) tau := by
                convert childLL hs332012 hx332012 hy332012 using 1 <;> norm_num
              exact Batch0318.cell2544.sound htau (by
                simp only [Batch0318.cell2544, Batch0318.tau2544, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320120 (by positivity) using 1 <;> norm_num)
            · have hs3320122 : InSquare (73/320) (103/320) (1/320) tau := by
                convert childUL hs332012 hx332012 hy332012 using 1 <;> norm_num
              exact Batch0318.cell2546.sound htau (by
                simp only [Batch0318.cell2546, Batch0318.tau2546, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy332012 | hy332012
            · have hs3320121 : InSquare (15/64) (101/320) (1/320) tau := by
                convert childLR hs332012 hx332012 hy332012 using 1 <;> norm_num
              exact Batch0318.cell2545.sound htau (by
                simp only [Batch0318.cell2545, Batch0318.tau2545, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320121 (by positivity) using 1 <;> norm_num)
            · have hs3320123 : InSquare (15/64) (103/320) (1/320) tau := by
                convert childUR hs332012 hx332012 hy332012 using 1 <;> norm_num
              exact Batch0318.cell2547.sound htau (by
                simp only [Batch0318.cell2547, Batch0318.tau2547, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy33201 | hy33201
        · have hs332011 : InSquare (39/160) (49/160) (1/160) tau := by
            convert childLR hs33201 hx33201 hy33201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx332011 | hx332011
          · rcases le_total tau.im (49/160 : ℝ) with hy332011 | hy332011
            · have hs3320110 : InSquare (77/320) (97/320) (1/320) tau := by
                convert childLL hs332011 hx332011 hy332011 using 1 <;> norm_num
              exact Batch0317.cell2540.sound htau (by
                simp only [Batch0317.cell2540, Batch0317.tau2540, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320110 (by positivity) using 1 <;> norm_num)
            · have hs3320112 : InSquare (77/320) (99/320) (1/320) tau := by
                convert childUL hs332011 hx332011 hy332011 using 1 <;> norm_num
              exact Batch0317.cell2542.sound htau (by
                simp only [Batch0317.cell2542, Batch0317.tau2542, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332011 | hy332011
            · have hs3320111 : InSquare (79/320) (97/320) (1/320) tau := by
                convert childLR hs332011 hx332011 hy332011 using 1 <;> norm_num
              exact Batch0317.cell2541.sound htau (by
                simp only [Batch0317.cell2541, Batch0317.tau2541, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320111 (by positivity) using 1 <;> norm_num)
            · have hs3320113 : InSquare (79/320) (99/320) (1/320) tau := by
                convert childUR hs332011 hx332011 hy332011 using 1 <;> norm_num
              exact Batch0317.cell2543.sound htau (by
                simp only [Batch0317.cell2543, Batch0317.tau2543, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320113 (by positivity) using 1 <;> norm_num)
        · have hs332013 : InSquare (39/160) (51/160) (1/160) tau := by
            convert childUR hs33201 hx33201 hy33201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx332013 | hx332013
          · rcases le_total tau.im (51/160 : ℝ) with hy332013 | hy332013
            · have hs3320130 : InSquare (77/320) (101/320) (1/320) tau := by
                convert childLL hs332013 hx332013 hy332013 using 1 <;> norm_num
              exact Batch0318.cell2548.sound htau (by
                simp only [Batch0318.cell2548, Batch0318.tau2548, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320130 (by positivity) using 1 <;> norm_num)
            · have hs3320132 : InSquare (77/320) (103/320) (1/320) tau := by
                convert childUL hs332013 hx332013 hy332013 using 1 <;> norm_num
              exact Batch0318.cell2550.sound htau (by
                simp only [Batch0318.cell2550, Batch0318.tau2550, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy332013 | hy332013
            · have hs3320131 : InSquare (79/320) (101/320) (1/320) tau := by
                convert childLR hs332013 hx332013 hy332013 using 1 <;> norm_num
              exact Batch0318.cell2549.sound htau (by
                simp only [Batch0318.cell2549, Batch0318.tau2549, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320131 (by positivity) using 1 <;> norm_num)
            · have hs3320133 : InSquare (79/320) (103/320) (1/320) tau := by
                convert childUR hs332013 hx332013 hy332013 using 1 <;> norm_num
              exact (outside_3320133 htau hs3320133).elim
    · have hs33203 : InSquare (19/80) (27/80) (1/80) tau := by
        convert childUR hs hx3320 hy3320 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33203 | hx33203
      · rcases le_total tau.im (27/80 : ℝ) with hy33203 | hy33203
        · have hs332030 : InSquare (37/160) (53/160) (1/160) tau := by
            convert childLL hs33203 hx33203 hy33203 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx332030 | hx332030
          · rcases le_total tau.im (53/160 : ℝ) with hy332030 | hy332030
            · have hs3320300 : InSquare (73/320) (21/64) (1/320) tau := by
                convert childLL hs332030 hx332030 hy332030 using 1 <;> norm_num
              exact Batch0319.cell2558.sound htau (by
                simp only [Batch0319.cell2558, Batch0319.tau2558, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3320300 (by positivity) using 1 <;> norm_num)
            · have hs3320302 : InSquare (73/320) (107/320) (1/320) tau := by
                convert childUL hs332030 hx332030 hy332030 using 1 <;> norm_num
              exact (outside_3320302 htau hs3320302).elim
          · rcases le_total tau.im (53/160 : ℝ) with hy332030 | hy332030
            · have hs3320301 : InSquare (15/64) (21/64) (1/320) tau := by
                convert childLR hs332030 hx332030 hy332030 using 1 <;> norm_num
              rcases le_total tau.re (15/64 : ℝ) with hx3320301 | hx3320301
              · rcases le_total tau.im (21/64 : ℝ) with hy3320301 | hy3320301
                · have hs33203010 : InSquare (149/640) (209/640) (1/640) tau := by
                    convert childLL hs3320301 hx3320301 hy3320301 using 1 <;> norm_num
                  exact Batch0480.cell3843.sound htau (by
                    simp only [Batch0480.cell3843, Batch0480.tau3843, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs33203010 (by positivity) using 1 <;> norm_num)
                · have hs33203012 : InSquare (149/640) (211/640) (1/640) tau := by
                    convert childUL hs3320301 hx3320301 hy3320301 using 1 <;> norm_num
                  exact (outside_33203012 htau hs33203012).elim
              · rcases le_total tau.im (21/64 : ℝ) with hy3320301 | hy3320301
                · have hs33203011 : InSquare (151/640) (209/640) (1/640) tau := by
                    convert childLR hs3320301 hx3320301 hy3320301 using 1 <;> norm_num
                  exact (outside_33203011 htau hs33203011).elim
                · have hs33203013 : InSquare (151/640) (211/640) (1/640) tau := by
                    convert childUR hs3320301 hx3320301 hy3320301 using 1 <;> norm_num
                  exact (outside_33203013 htau hs33203013).elim
            · have hs3320303 : InSquare (15/64) (107/320) (1/320) tau := by
                convert childUR hs332030 hx332030 hy332030 using 1 <;> norm_num
              exact (outside_3320303 htau hs3320303).elim
        · have hs332032 : InSquare (37/160) (11/32) (1/160) tau := by
            convert childUL hs33203 hx33203 hy33203 using 1 <;> norm_num
          exact (outside_332032 htau hs332032).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy33203 | hy33203
        · have hs332031 : InSquare (39/160) (53/160) (1/160) tau := by
            convert childLR hs33203 hx33203 hy33203 using 1 <;> norm_num
          exact (outside_332031 htau hs332031).elim
        · have hs332033 : InSquare (39/160) (11/32) (1/160) tau := by
            convert childUR hs33203 hx33203 hy33203 using 1 <;> norm_num
          exact (outside_332033 htau hs332033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3320

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_33211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/64) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3321 | hx3321
  · rcases le_total tau.im (13/40 : ℝ) with hy3321 | hy3321
    · have hs33210 : InSquare (21/80) (5/16) (1/80) tau := by
        convert childLL hs hx3321 hy3321 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33210 | hx33210
      · rcases le_total tau.im (5/16 : ℝ) with hy33210 | hy33210
        · have hs332100 : InSquare (41/160) (49/160) (1/160) tau := by
            convert childLL hs33210 hx33210 hy33210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx332100 | hx332100
          · rcases le_total tau.im (49/160 : ℝ) with hy332100 | hy332100
            · have hs3321000 : InSquare (81/320) (97/320) (1/320) tau := by
                convert childLL hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0319.cell2559.sound htau (by
                simp only [Batch0319.cell2559, Batch0319.tau2559, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321000 (by positivity) using 1 <;> norm_num)
            · have hs3321002 : InSquare (81/320) (99/320) (1/320) tau := by
                convert childUL hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2561.sound htau (by
                simp only [Batch0320.cell2561, Batch0320.tau2561, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332100 | hy332100
            · have hs3321001 : InSquare (83/320) (97/320) (1/320) tau := by
                convert childLR hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2560.sound htau (by
                simp only [Batch0320.cell2560, Batch0320.tau2560, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321001 (by positivity) using 1 <;> norm_num)
            · have hs3321003 : InSquare (83/320) (99/320) (1/320) tau := by
                convert childUR hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2562.sound htau (by
                simp only [Batch0320.cell2562, Batch0320.tau2562, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321003 (by positivity) using 1 <;> norm_num)
        · have hs332102 : InSquare (41/160) (51/160) (1/160) tau := by
            convert childUL hs33210 hx33210 hy33210 using 1 <;> norm_num
          exact (outside_332102 htau hs332102).elim
      · rcases le_total tau.im (5/16 : ℝ) with hy33210 | hy33210
        · have hs332101 : InSquare (43/160) (49/160) (1/160) tau := by
            convert childLR hs33210 hx33210 hy33210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx332101 | hx332101
          · rcases le_total tau.im (49/160 : ℝ) with hy332101 | hy332101
            · have hs3321010 : InSquare (17/64) (97/320) (1/320) tau := by
                convert childLL hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact Batch0320.cell2563.sound htau (by
                simp only [Batch0320.cell2563, Batch0320.tau2563, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321010 (by positivity) using 1 <;> norm_num)
            · have hs3321012 : InSquare (17/64) (99/320) (1/320) tau := by
                convert childUL hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321012 htau hs3321012).elim
          · rcases le_total tau.im (49/160 : ℝ) with hy332101 | hy332101
            · have hs3321011 : InSquare (87/320) (97/320) (1/320) tau := by
                convert childLR hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321011 htau hs3321011).elim
            · have hs3321013 : InSquare (87/320) (99/320) (1/320) tau := by
                convert childUR hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321013 htau hs3321013).elim
        · have hs332103 : InSquare (43/160) (51/160) (1/160) tau := by
            convert childUR hs33210 hx33210 hy33210 using 1 <;> norm_num
          exact (outside_332103 htau hs332103).elim
    · have hs33212 : InSquare (21/80) (27/80) (1/80) tau := by
        convert childUL hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33212 htau hs33212).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy3321 | hy3321
    · have hs33211 : InSquare (23/80) (5/16) (1/80) tau := by
        convert childLR hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33211 htau hs33211).elim
    · have hs33213 : InSquare (23/80) (27/80) (1/80) tau := by
        convert childUR hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33213 htau hs33213).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321

end


