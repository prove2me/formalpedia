-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3132__13
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3132__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:17:24.103751+00:00
-- url     : https://prove2.me/theorems/4766aafa-d5dd-41ad-b019-976bba0c7c29
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132 (+12 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132 (+12 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132 (+12 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132 (+12 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3132 (+12 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3133, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3200, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3201, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3202, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3203, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3210, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3211, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3212, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3213, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3220, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3221, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3222).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0131
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0132
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0277
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0040
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0041
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0137
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0138
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0141
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0142
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0278
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0279
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0280
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0283
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0284
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0441
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0442
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0446
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3132 | hx3132
  · rcases le_total tau.im (7/40 : ℝ) with hy3132 | hy3132
    · have hs31320 : InSquare (5/16) (13/80) (1/80) tau := by
        convert childLL hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31320 | hx31320
      · rcases le_total tau.im (13/80 : ℝ) with hy31320 | hy31320
        · have hs313200 : InSquare (49/160) (5/32) (1/160) tau := by
            convert childLL hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1042.sound htau (by
            simp only [Batch0130.cell1042, Batch0130.tau1042, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313200 (by positivity) using 1 <;> norm_num)
        · have hs313202 : InSquare (49/160) (27/160) (1/160) tau := by
            convert childUL hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1044.sound htau (by
            simp only [Batch0130.cell1044, Batch0130.tau1044, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31320 | hy31320
        · have hs313201 : InSquare (51/160) (5/32) (1/160) tau := by
            convert childLR hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1043.sound htau (by
            simp only [Batch0130.cell1043, Batch0130.tau1043, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313201 (by positivity) using 1 <;> norm_num)
        · have hs313203 : InSquare (51/160) (27/160) (1/160) tau := by
            convert childUR hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1045.sound htau (by
            simp only [Batch0130.cell1045, Batch0130.tau1045, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313203 (by positivity) using 1 <;> norm_num)
    · have hs31322 : InSquare (5/16) (3/16) (1/80) tau := by
        convert childUL hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31322 | hx31322
      · rcases le_total tau.im (3/16 : ℝ) with hy31322 | hy31322
        · have hs313220 : InSquare (49/160) (29/160) (1/160) tau := by
            convert childLL hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1050.sound htau (by
            simp only [Batch0131.cell1050, Batch0131.tau1050, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313220 (by positivity) using 1 <;> norm_num)
        · have hs313222 : InSquare (49/160) (31/160) (1/160) tau := by
            convert childUL hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1052.sound htau (by
            simp only [Batch0131.cell1052, Batch0131.tau1052, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31322 | hy31322
        · have hs313221 : InSquare (51/160) (29/160) (1/160) tau := by
            convert childLR hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1051.sound htau (by
            simp only [Batch0131.cell1051, Batch0131.tau1051, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313221 (by positivity) using 1 <;> norm_num)
        · have hs313223 : InSquare (51/160) (31/160) (1/160) tau := by
            convert childUR hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1053.sound htau (by
            simp only [Batch0131.cell1053, Batch0131.tau1053, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3132 | hy3132
    · have hs31321 : InSquare (27/80) (13/80) (1/80) tau := by
        convert childLR hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31321 | hx31321
      · rcases le_total tau.im (13/80 : ℝ) with hy31321 | hy31321
        · have hs313210 : InSquare (53/160) (5/32) (1/160) tau := by
            convert childLL hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0130.cell1046.sound htau (by
            simp only [Batch0130.cell1046, Batch0130.tau1046, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313210 (by positivity) using 1 <;> norm_num)
        · have hs313212 : InSquare (53/160) (27/160) (1/160) tau := by
            convert childUL hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0131.cell1048.sound htau (by
            simp only [Batch0131.cell1048, Batch0131.tau1048, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31321 | hy31321
        · have hs313211 : InSquare (11/32) (5/32) (1/160) tau := by
            convert childLR hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0130.cell1047.sound htau (by
            simp only [Batch0130.cell1047, Batch0130.tau1047, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313211 (by positivity) using 1 <;> norm_num)
        · have hs313213 : InSquare (11/32) (27/160) (1/160) tau := by
            convert childUR hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0131.cell1049.sound htau (by
            simp only [Batch0131.cell1049, Batch0131.tau1049, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313213 (by positivity) using 1 <;> norm_num)
    · have hs31323 : InSquare (27/80) (3/16) (1/80) tau := by
        convert childUR hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31323 | hx31323
      · rcases le_total tau.im (3/16 : ℝ) with hy31323 | hy31323
        · have hs313230 : InSquare (53/160) (29/160) (1/160) tau := by
            convert childLL hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0131.cell1054.sound htau (by
            simp only [Batch0131.cell1054, Batch0131.tau1054, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313230 (by positivity) using 1 <;> norm_num)
        · have hs313232 : InSquare (53/160) (31/160) (1/160) tau := by
            convert childUL hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0132.cell1056.sound htau (by
            simp only [Batch0132.cell1056, Batch0132.tau1056, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31323 | hy31323
        · have hs313231 : InSquare (11/32) (29/160) (1/160) tau := by
            convert childLR hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0131.cell1055.sound htau (by
            simp only [Batch0131.cell1055, Batch0131.tau1055, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313231 (by positivity) using 1 <;> norm_num)
        · have hs313233 : InSquare (11/32) (31/160) (1/160) tau := by
            convert childUR hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0132.cell1057.sound htau (by
            simp only [Batch0132.cell1057, Batch0132.tau1057, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_31331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_31333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133221 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (113/320) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3133 | hx3133
  · rcases le_total tau.im (7/40 : ℝ) with hy3133 | hy3133
    · have hs31330 : InSquare (29/80) (13/80) (1/80) tau := by
        convert childLL hs hx3133 hy3133 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31330 | hx31330
      · rcases le_total tau.im (13/80 : ℝ) with hy31330 | hy31330
        · have hs313300 : InSquare (57/160) (5/32) (1/160) tau := by
            convert childLL hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1058.sound htau (by
            simp only [Batch0132.cell1058, Batch0132.tau1058, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313300 (by positivity) using 1 <;> norm_num)
        · have hs313302 : InSquare (57/160) (27/160) (1/160) tau := by
            convert childUL hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1060.sound htau (by
            simp only [Batch0132.cell1060, Batch0132.tau1060, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31330 | hy31330
        · have hs313301 : InSquare (59/160) (5/32) (1/160) tau := by
            convert childLR hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1059.sound htau (by
            simp only [Batch0132.cell1059, Batch0132.tau1059, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313301 (by positivity) using 1 <;> norm_num)
        · have hs313303 : InSquare (59/160) (27/160) (1/160) tau := by
            convert childUR hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1061.sound htau (by
            simp only [Batch0132.cell1061, Batch0132.tau1061, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313303 (by positivity) using 1 <;> norm_num)
    · have hs31332 : InSquare (29/80) (3/16) (1/80) tau := by
        convert childUL hs hx3133 hy3133 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31332 | hx31332
      · rcases le_total tau.im (3/16 : ℝ) with hy31332 | hy31332
        · have hs313320 : InSquare (57/160) (29/160) (1/160) tau := by
            convert childLL hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact Batch0132.cell1062.sound htau (by
            simp only [Batch0132.cell1062, Batch0132.tau1062, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313320 (by positivity) using 1 <;> norm_num)
        · have hs313322 : InSquare (57/160) (31/160) (1/160) tau := by
            convert childUL hs31332 hx31332 hy31332 using 1 <;> norm_num
          rcases le_total tau.re (57/160 : ℝ) with hx313322 | hx313322
          · rcases le_total tau.im (31/160 : ℝ) with hy313322 | hy313322
            · have hs3133220 : InSquare (113/320) (61/320) (1/320) tau := by
                convert childLL hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact Batch0277.cell2223.sound htau (by
                simp only [Batch0277.cell2223, Batch0277.tau2223, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3133220 (by positivity) using 1 <;> norm_num)
            · have hs3133222 : InSquare (113/320) (63/320) (1/320) tau := by
                convert childUL hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133222 htau hs3133222).elim
          · rcases le_total tau.im (31/160 : ℝ) with hy313322 | hy313322
            · have hs3133221 : InSquare (23/64) (61/320) (1/320) tau := by
                convert childLR hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133221 htau hs3133221).elim
            · have hs3133223 : InSquare (23/64) (63/320) (1/320) tau := by
                convert childUR hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133223 htau hs3133223).elim
      · rcases le_total tau.im (3/16 : ℝ) with hy31332 | hy31332
        · have hs313321 : InSquare (59/160) (29/160) (1/160) tau := by
            convert childLR hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact (outside_313321 htau hs313321).elim
        · have hs313323 : InSquare (59/160) (31/160) (1/160) tau := by
            convert childUR hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact (outside_313323 htau hs313323).elim
  · rcases le_total tau.im (7/40 : ℝ) with hy3133 | hy3133
    · have hs31331 : InSquare (31/80) (13/80) (1/80) tau := by
        convert childLR hs hx3133 hy3133 using 1 <;> norm_num
      exact (outside_31331 htau hs31331).elim
    · have hs31333 : InSquare (31/80) (3/16) (1/80) tau := by
        convert childUR hs hx3133 hy3133 using 1 <;> norm_num
      exact (outside_31333 htau hs31333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3200 | hx3200
  · rcases le_total tau.im (9/40 : ℝ) with hy3200 | hy3200
    · have hs32000 : InSquare (1/80) (17/80) (1/80) tau := by
        convert childLL hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0324.sound htau (by
        simp only [Batch0040.cell0324, Batch0040.tau0324, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32000 (by positivity) using 1 <;> norm_num)
    · have hs32002 : InSquare (1/80) (19/80) (1/80) tau := by
        convert childUL hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0326.sound htau (by
        simp only [Batch0040.cell0326, Batch0040.tau0326, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32002 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3200 | hy3200
    · have hs32001 : InSquare (3/80) (17/80) (1/80) tau := by
        convert childLR hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0325.sound htau (by
        simp only [Batch0040.cell0325, Batch0040.tau0325, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32001 (by positivity) using 1 <;> norm_num)
    · have hs32003 : InSquare (3/80) (19/80) (1/80) tau := by
        convert childUR hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0327.sound htau (by
        simp only [Batch0040.cell0327, Batch0040.tau0327, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3201 | hx3201
  · rcases le_total tau.im (9/40 : ℝ) with hy3201 | hy3201
    · have hs32010 : InSquare (1/16) (17/80) (1/80) tau := by
        convert childLL hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0328.sound htau (by
        simp only [Batch0041.cell0328, Batch0041.tau0328, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32010 (by positivity) using 1 <;> norm_num)
    · have hs32012 : InSquare (1/16) (19/80) (1/80) tau := by
        convert childUL hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0330.sound htau (by
        simp only [Batch0041.cell0330, Batch0041.tau0330, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3201 | hy3201
    · have hs32011 : InSquare (7/80) (17/80) (1/80) tau := by
        convert childLR hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0329.sound htau (by
        simp only [Batch0041.cell0329, Batch0041.tau0329, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32011 (by positivity) using 1 <;> norm_num)
    · have hs32013 : InSquare (7/80) (19/80) (1/80) tau := by
        convert childUR hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0331.sound htau (by
        simp only [Batch0041.cell0331, Batch0041.tau0331, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3202 | hx3202
  · rcases le_total tau.im (11/40 : ℝ) with hy3202 | hy3202
    · have hs32020 : InSquare (1/80) (21/80) (1/80) tau := by
        convert childLL hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0332.sound htau (by
        simp only [Batch0041.cell0332, Batch0041.tau0332, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32020 (by positivity) using 1 <;> norm_num)
    · have hs32022 : InSquare (1/80) (23/80) (1/80) tau := by
        convert childUL hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0334.sound htau (by
        simp only [Batch0041.cell0334, Batch0041.tau0334, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3202 | hy3202
    · have hs32021 : InSquare (3/80) (21/80) (1/80) tau := by
        convert childLR hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0333.sound htau (by
        simp only [Batch0041.cell0333, Batch0041.tau0333, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32021 (by positivity) using 1 <;> norm_num)
    · have hs32023 : InSquare (3/80) (23/80) (1/80) tau := by
        convert childUR hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0335.sound htau (by
        simp only [Batch0041.cell0335, Batch0041.tau0335, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3203 | hx3203
  · rcases le_total tau.im (11/40 : ℝ) with hy3203 | hy3203
    · have hs32030 : InSquare (1/16) (21/80) (1/80) tau := by
        convert childLL hs hx3203 hy3203 using 1 <;> norm_num
      exact Batch0042.cell0336.sound htau (by
        simp only [Batch0042.cell0336, Batch0042.tau0336, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32030 (by positivity) using 1 <;> norm_num)
    · have hs32032 : InSquare (1/16) (23/80) (1/80) tau := by
        convert childUL hs hx3203 hy3203 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32032 | hx32032
      · rcases le_total tau.im (23/80 : ℝ) with hy32032 | hy32032
        · have hs320320 : InSquare (9/160) (9/32) (1/160) tau := by
            convert childLL hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0132.cell1063.sound htau (by
            simp only [Batch0132.cell1063, Batch0132.tau1063, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320320 (by positivity) using 1 <;> norm_num)
        · have hs320322 : InSquare (9/160) (47/160) (1/160) tau := by
            convert childUL hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1065.sound htau (by
            simp only [Batch0133.cell1065, Batch0133.tau1065, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32032 | hy32032
        · have hs320321 : InSquare (11/160) (9/32) (1/160) tau := by
            convert childLR hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1064.sound htau (by
            simp only [Batch0133.cell1064, Batch0133.tau1064, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320321 (by positivity) using 1 <;> norm_num)
        · have hs320323 : InSquare (11/160) (47/160) (1/160) tau := by
            convert childUR hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1066.sound htau (by
            simp only [Batch0133.cell1066, Batch0133.tau1066, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3203 | hy3203
    · have hs32031 : InSquare (7/80) (21/80) (1/80) tau := by
        convert childLR hs hx3203 hy3203 using 1 <;> norm_num
      exact Batch0042.cell0337.sound htau (by
        simp only [Batch0042.cell0337, Batch0042.tau0337, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32031 (by positivity) using 1 <;> norm_num)
    · have hs32033 : InSquare (7/80) (23/80) (1/80) tau := by
        convert childUR hs hx3203 hy3203 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32033 | hx32033
      · rcases le_total tau.im (23/80 : ℝ) with hy32033 | hy32033
        · have hs320330 : InSquare (13/160) (9/32) (1/160) tau := by
            convert childLL hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1067.sound htau (by
            simp only [Batch0133.cell1067, Batch0133.tau1067, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320330 (by positivity) using 1 <;> norm_num)
        · have hs320332 : InSquare (13/160) (47/160) (1/160) tau := by
            convert childUL hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1069.sound htau (by
            simp only [Batch0133.cell1069, Batch0133.tau1069, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32033 | hy32033
        · have hs320331 : InSquare (3/32) (9/32) (1/160) tau := by
            convert childLR hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1068.sound htau (by
            simp only [Batch0133.cell1068, Batch0133.tau1068, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320331 (by positivity) using 1 <;> norm_num)
        · have hs320333 : InSquare (3/32) (47/160) (1/160) tau := by
            convert childUR hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1070.sound htau (by
            simp only [Batch0133.cell1070, Batch0133.tau1070, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3210 | hx3210
  · rcases le_total tau.im (9/40 : ℝ) with hy3210 | hy3210
    · have hs32100 : InSquare (9/80) (17/80) (1/80) tau := by
        convert childLL hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0338.sound htau (by
        simp only [Batch0042.cell0338, Batch0042.tau0338, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32100 (by positivity) using 1 <;> norm_num)
    · have hs32102 : InSquare (9/80) (19/80) (1/80) tau := by
        convert childUL hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0340.sound htau (by
        simp only [Batch0042.cell0340, Batch0042.tau0340, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3210 | hy3210
    · have hs32101 : InSquare (11/80) (17/80) (1/80) tau := by
        convert childLR hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0339.sound htau (by
        simp only [Batch0042.cell0339, Batch0042.tau0339, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32101 (by positivity) using 1 <;> norm_num)
    · have hs32103 : InSquare (11/80) (19/80) (1/80) tau := by
        convert childUR hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0341.sound htau (by
        simp only [Batch0042.cell0341, Batch0042.tau0341, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3211 | hx3211
  · rcases le_total tau.im (9/40 : ℝ) with hy3211 | hy3211
    · have hs32110 : InSquare (13/80) (17/80) (1/80) tau := by
        convert childLL hs hx3211 hy3211 using 1 <;> norm_num
      exact Batch0042.cell0342.sound htau (by
        simp only [Batch0042.cell0342, Batch0042.tau0342, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32110 (by positivity) using 1 <;> norm_num)
    · have hs32112 : InSquare (13/80) (19/80) (1/80) tau := by
        convert childUL hs hx3211 hy3211 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32112 | hx32112
      · rcases le_total tau.im (19/80 : ℝ) with hy32112 | hy32112
        · have hs321120 : InSquare (5/32) (37/160) (1/160) tau := by
            convert childLL hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0133.cell1071.sound htau (by
            simp only [Batch0133.cell1071, Batch0133.tau1071, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321120 (by positivity) using 1 <;> norm_num)
        · have hs321122 : InSquare (5/32) (39/160) (1/160) tau := by
            convert childUL hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1073.sound htau (by
            simp only [Batch0134.cell1073, Batch0134.tau1073, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy32112 | hy32112
        · have hs321121 : InSquare (27/160) (37/160) (1/160) tau := by
            convert childLR hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1072.sound htau (by
            simp only [Batch0134.cell1072, Batch0134.tau1072, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321121 (by positivity) using 1 <;> norm_num)
        · have hs321123 : InSquare (27/160) (39/160) (1/160) tau := by
            convert childUR hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1074.sound htau (by
            simp only [Batch0134.cell1074, Batch0134.tau1074, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3211 | hy3211
    · have hs32111 : InSquare (3/16) (17/80) (1/80) tau := by
        convert childLR hs hx3211 hy3211 using 1 <;> norm_num
      exact Batch0042.cell0343.sound htau (by
        simp only [Batch0042.cell0343, Batch0042.tau0343, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32111 (by positivity) using 1 <;> norm_num)
    · have hs32113 : InSquare (3/16) (19/80) (1/80) tau := by
        convert childUR hs hx3211 hy3211 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32113 | hx32113
      · rcases le_total tau.im (19/80 : ℝ) with hy32113 | hy32113
        · have hs321130 : InSquare (29/160) (37/160) (1/160) tau := by
            convert childLL hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1075.sound htau (by
            simp only [Batch0134.cell1075, Batch0134.tau1075, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321130 (by positivity) using 1 <;> norm_num)
        · have hs321132 : InSquare (29/160) (39/160) (1/160) tau := by
            convert childUL hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1077.sound htau (by
            simp only [Batch0134.cell1077, Batch0134.tau1077, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy32113 | hy32113
        · have hs321131 : InSquare (31/160) (37/160) (1/160) tau := by
            convert childLR hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1076.sound htau (by
            simp only [Batch0134.cell1076, Batch0134.tau1076, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321131 (by positivity) using 1 <;> norm_num)
        · have hs321133 : InSquare (31/160) (39/160) (1/160) tau := by
            convert childUR hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1078.sound htau (by
            simp only [Batch0134.cell1078, Batch0134.tau1078, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3212 | hx3212
  · rcases le_total tau.im (11/40 : ℝ) with hy3212 | hy3212
    · have hs32120 : InSquare (9/80) (21/80) (1/80) tau := by
        convert childLL hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32120 | hx32120
      · rcases le_total tau.im (21/80 : ℝ) with hy32120 | hy32120
        · have hs321200 : InSquare (17/160) (41/160) (1/160) tau := by
            convert childLL hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0134.cell1079.sound htau (by
            simp only [Batch0134.cell1079, Batch0134.tau1079, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321200 (by positivity) using 1 <;> norm_num)
        · have hs321202 : InSquare (17/160) (43/160) (1/160) tau := by
            convert childUL hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1081.sound htau (by
            simp only [Batch0135.cell1081, Batch0135.tau1081, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32120 | hy32120
        · have hs321201 : InSquare (19/160) (41/160) (1/160) tau := by
            convert childLR hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1080.sound htau (by
            simp only [Batch0135.cell1080, Batch0135.tau1080, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321201 (by positivity) using 1 <;> norm_num)
        · have hs321203 : InSquare (19/160) (43/160) (1/160) tau := by
            convert childUR hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1082.sound htau (by
            simp only [Batch0135.cell1082, Batch0135.tau1082, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321203 (by positivity) using 1 <;> norm_num)
    · have hs32122 : InSquare (9/80) (23/80) (1/80) tau := by
        convert childUL hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32122 | hx32122
      · rcases le_total tau.im (23/80 : ℝ) with hy32122 | hy32122
        · have hs321220 : InSquare (17/160) (9/32) (1/160) tau := by
            convert childLL hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0135.cell1087.sound htau (by
            simp only [Batch0135.cell1087, Batch0135.tau1087, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321220 (by positivity) using 1 <;> norm_num)
        · have hs321222 : InSquare (17/160) (47/160) (1/160) tau := by
            convert childUL hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1089.sound htau (by
            simp only [Batch0136.cell1089, Batch0136.tau1089, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32122 | hy32122
        · have hs321221 : InSquare (19/160) (9/32) (1/160) tau := by
            convert childLR hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1088.sound htau (by
            simp only [Batch0136.cell1088, Batch0136.tau1088, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321221 (by positivity) using 1 <;> norm_num)
        · have hs321223 : InSquare (19/160) (47/160) (1/160) tau := by
            convert childUR hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1090.sound htau (by
            simp only [Batch0136.cell1090, Batch0136.tau1090, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3212 | hy3212
    · have hs32121 : InSquare (11/80) (21/80) (1/80) tau := by
        convert childLR hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32121 | hx32121
      · rcases le_total tau.im (21/80 : ℝ) with hy32121 | hy32121
        · have hs321210 : InSquare (21/160) (41/160) (1/160) tau := by
            convert childLL hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1083.sound htau (by
            simp only [Batch0135.cell1083, Batch0135.tau1083, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321210 (by positivity) using 1 <;> norm_num)
        · have hs321212 : InSquare (21/160) (43/160) (1/160) tau := by
            convert childUL hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1085.sound htau (by
            simp only [Batch0135.cell1085, Batch0135.tau1085, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32121 | hy32121
        · have hs321211 : InSquare (23/160) (41/160) (1/160) tau := by
            convert childLR hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1084.sound htau (by
            simp only [Batch0135.cell1084, Batch0135.tau1084, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321211 (by positivity) using 1 <;> norm_num)
        · have hs321213 : InSquare (23/160) (43/160) (1/160) tau := by
            convert childUR hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1086.sound htau (by
            simp only [Batch0135.cell1086, Batch0135.tau1086, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321213 (by positivity) using 1 <;> norm_num)
    · have hs32123 : InSquare (11/80) (23/80) (1/80) tau := by
        convert childUR hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32123 | hx32123
      · rcases le_total tau.im (23/80 : ℝ) with hy32123 | hy32123
        · have hs321230 : InSquare (21/160) (9/32) (1/160) tau := by
            convert childLL hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1091.sound htau (by
            simp only [Batch0136.cell1091, Batch0136.tau1091, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321230 (by positivity) using 1 <;> norm_num)
        · have hs321232 : InSquare (21/160) (47/160) (1/160) tau := by
            convert childUL hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1093.sound htau (by
            simp only [Batch0136.cell1093, Batch0136.tau1093, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32123 | hy32123
        · have hs321231 : InSquare (23/160) (9/32) (1/160) tau := by
            convert childLR hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1092.sound htau (by
            simp only [Batch0136.cell1092, Batch0136.tau1092, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321231 (by positivity) using 1 <;> norm_num)
        · have hs321233 : InSquare (23/160) (47/160) (1/160) tau := by
            convert childUR hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1094.sound htau (by
            simp only [Batch0136.cell1094, Batch0136.tau1094, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3213 | hx3213
  · rcases le_total tau.im (11/40 : ℝ) with hy3213 | hy3213
    · have hs32130 : InSquare (13/80) (21/80) (1/80) tau := by
        convert childLL hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32130 | hx32130
      · rcases le_total tau.im (21/80 : ℝ) with hy32130 | hy32130
        · have hs321300 : InSquare (5/32) (41/160) (1/160) tau := by
            convert childLL hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0136.cell1095.sound htau (by
            simp only [Batch0136.cell1095, Batch0136.tau1095, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321300 (by positivity) using 1 <;> norm_num)
        · have hs321302 : InSquare (5/32) (43/160) (1/160) tau := by
            convert childUL hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1097.sound htau (by
            simp only [Batch0137.cell1097, Batch0137.tau1097, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32130 | hy32130
        · have hs321301 : InSquare (27/160) (41/160) (1/160) tau := by
            convert childLR hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1096.sound htau (by
            simp only [Batch0137.cell1096, Batch0137.tau1096, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321301 (by positivity) using 1 <;> norm_num)
        · have hs321303 : InSquare (27/160) (43/160) (1/160) tau := by
            convert childUR hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1098.sound htau (by
            simp only [Batch0137.cell1098, Batch0137.tau1098, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321303 (by positivity) using 1 <;> norm_num)
    · have hs32132 : InSquare (13/80) (23/80) (1/80) tau := by
        convert childUL hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32132 | hx32132
      · rcases le_total tau.im (23/80 : ℝ) with hy32132 | hy32132
        · have hs321320 : InSquare (5/32) (9/32) (1/160) tau := by
            convert childLL hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0137.cell1103.sound htau (by
            simp only [Batch0137.cell1103, Batch0137.tau1103, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321320 (by positivity) using 1 <;> norm_num)
        · have hs321322 : InSquare (5/32) (47/160) (1/160) tau := by
            convert childUL hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1105.sound htau (by
            simp only [Batch0138.cell1105, Batch0138.tau1105, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32132 | hy32132
        · have hs321321 : InSquare (27/160) (9/32) (1/160) tau := by
            convert childLR hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1104.sound htau (by
            simp only [Batch0138.cell1104, Batch0138.tau1104, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321321 (by positivity) using 1 <;> norm_num)
        · have hs321323 : InSquare (27/160) (47/160) (1/160) tau := by
            convert childUR hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1106.sound htau (by
            simp only [Batch0138.cell1106, Batch0138.tau1106, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3213 | hy3213
    · have hs32131 : InSquare (3/16) (21/80) (1/80) tau := by
        convert childLR hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32131 | hx32131
      · rcases le_total tau.im (21/80 : ℝ) with hy32131 | hy32131
        · have hs321310 : InSquare (29/160) (41/160) (1/160) tau := by
            convert childLL hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1099.sound htau (by
            simp only [Batch0137.cell1099, Batch0137.tau1099, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321310 (by positivity) using 1 <;> norm_num)
        · have hs321312 : InSquare (29/160) (43/160) (1/160) tau := by
            convert childUL hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1101.sound htau (by
            simp only [Batch0137.cell1101, Batch0137.tau1101, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32131 | hy32131
        · have hs321311 : InSquare (31/160) (41/160) (1/160) tau := by
            convert childLR hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1100.sound htau (by
            simp only [Batch0137.cell1100, Batch0137.tau1100, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321311 (by positivity) using 1 <;> norm_num)
        · have hs321313 : InSquare (31/160) (43/160) (1/160) tau := by
            convert childUR hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1102.sound htau (by
            simp only [Batch0137.cell1102, Batch0137.tau1102, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321313 (by positivity) using 1 <;> norm_num)
    · have hs32133 : InSquare (3/16) (23/80) (1/80) tau := by
        convert childUR hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32133 | hx32133
      · rcases le_total tau.im (23/80 : ℝ) with hy32133 | hy32133
        · have hs321330 : InSquare (29/160) (9/32) (1/160) tau := by
            convert childLL hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1107.sound htau (by
            simp only [Batch0138.cell1107, Batch0138.tau1107, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321330 (by positivity) using 1 <;> norm_num)
        · have hs321332 : InSquare (29/160) (47/160) (1/160) tau := by
            convert childUL hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1109.sound htau (by
            simp only [Batch0138.cell1109, Batch0138.tau1109, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32133 | hy32133
        · have hs321331 : InSquare (31/160) (9/32) (1/160) tau := by
            convert childLR hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1108.sound htau (by
            simp only [Batch0138.cell1108, Batch0138.tau1108, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321331 (by positivity) using 1 <;> norm_num)
        · have hs321333 : InSquare (31/160) (47/160) (1/160) tau := by
            convert childUR hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1110.sound htau (by
            simp only [Batch0138.cell1110, Batch0138.tau1110, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3220 | hx3220
  · rcases le_total tau.im (13/40 : ℝ) with hy3220 | hy3220
    · have hs32200 : InSquare (1/80) (5/16) (1/80) tau := by
        convert childLL hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32200 | hx32200
      · rcases le_total tau.im (5/16 : ℝ) with hy32200 | hy32200
        · have hs322000 : InSquare (1/160) (49/160) (1/160) tau := by
            convert childLL hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0138.cell1111.sound htau (by
            simp only [Batch0138.cell1111, Batch0138.tau1111, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322000 (by positivity) using 1 <;> norm_num)
        · have hs322002 : InSquare (1/160) (51/160) (1/160) tau := by
            convert childUL hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1113.sound htau (by
            simp only [Batch0139.cell1113, Batch0139.tau1113, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32200 | hy32200
        · have hs322001 : InSquare (3/160) (49/160) (1/160) tau := by
            convert childLR hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1112.sound htau (by
            simp only [Batch0139.cell1112, Batch0139.tau1112, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322001 (by positivity) using 1 <;> norm_num)
        · have hs322003 : InSquare (3/160) (51/160) (1/160) tau := by
            convert childUR hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1114.sound htau (by
            simp only [Batch0139.cell1114, Batch0139.tau1114, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322003 (by positivity) using 1 <;> norm_num)
    · have hs32202 : InSquare (1/80) (27/80) (1/80) tau := by
        convert childUL hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32202 | hx32202
      · rcases le_total tau.im (27/80 : ℝ) with hy32202 | hy32202
        · have hs322020 : InSquare (1/160) (53/160) (1/160) tau := by
            convert childLL hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0139.cell1119.sound htau (by
            simp only [Batch0139.cell1119, Batch0139.tau1119, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322020 (by positivity) using 1 <;> norm_num)
        · have hs322022 : InSquare (1/160) (11/32) (1/160) tau := by
            convert childUL hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1121.sound htau (by
            simp only [Batch0140.cell1121, Batch0140.tau1121, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32202 | hy32202
        · have hs322021 : InSquare (3/160) (53/160) (1/160) tau := by
            convert childLR hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1120.sound htau (by
            simp only [Batch0140.cell1120, Batch0140.tau1120, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322021 (by positivity) using 1 <;> norm_num)
        · have hs322023 : InSquare (3/160) (11/32) (1/160) tau := by
            convert childUR hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1122.sound htau (by
            simp only [Batch0140.cell1122, Batch0140.tau1122, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3220 | hy3220
    · have hs32201 : InSquare (3/80) (5/16) (1/80) tau := by
        convert childLR hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32201 | hx32201
      · rcases le_total tau.im (5/16 : ℝ) with hy32201 | hy32201
        · have hs322010 : InSquare (1/32) (49/160) (1/160) tau := by
            convert childLL hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1115.sound htau (by
            simp only [Batch0139.cell1115, Batch0139.tau1115, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322010 (by positivity) using 1 <;> norm_num)
        · have hs322012 : InSquare (1/32) (51/160) (1/160) tau := by
            convert childUL hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1117.sound htau (by
            simp only [Batch0139.cell1117, Batch0139.tau1117, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32201 | hy32201
        · have hs322011 : InSquare (7/160) (49/160) (1/160) tau := by
            convert childLR hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1116.sound htau (by
            simp only [Batch0139.cell1116, Batch0139.tau1116, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322011 (by positivity) using 1 <;> norm_num)
        · have hs322013 : InSquare (7/160) (51/160) (1/160) tau := by
            convert childUR hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1118.sound htau (by
            simp only [Batch0139.cell1118, Batch0139.tau1118, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322013 (by positivity) using 1 <;> norm_num)
    · have hs32203 : InSquare (3/80) (27/80) (1/80) tau := by
        convert childUR hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32203 | hx32203
      · rcases le_total tau.im (27/80 : ℝ) with hy32203 | hy32203
        · have hs322030 : InSquare (1/32) (53/160) (1/160) tau := by
            convert childLL hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1123.sound htau (by
            simp only [Batch0140.cell1123, Batch0140.tau1123, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322030 (by positivity) using 1 <;> norm_num)
        · have hs322032 : InSquare (1/32) (11/32) (1/160) tau := by
            convert childUL hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1125.sound htau (by
            simp only [Batch0140.cell1125, Batch0140.tau1125, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32203 | hy32203
        · have hs322031 : InSquare (7/160) (53/160) (1/160) tau := by
            convert childLR hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1124.sound htau (by
            simp only [Batch0140.cell1124, Batch0140.tau1124, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322031 (by positivity) using 1 <;> norm_num)
        · have hs322033 : InSquare (7/160) (11/32) (1/160) tau := by
            convert childUR hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1126.sound htau (by
            simp only [Batch0140.cell1126, Batch0140.tau1126, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3221 | hx3221
  · rcases le_total tau.im (13/40 : ℝ) with hy3221 | hy3221
    · have hs32210 : InSquare (1/16) (5/16) (1/80) tau := by
        convert childLL hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32210 | hx32210
      · rcases le_total tau.im (5/16 : ℝ) with hy32210 | hy32210
        · have hs322100 : InSquare (9/160) (49/160) (1/160) tau := by
            convert childLL hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0140.cell1127.sound htau (by
            simp only [Batch0140.cell1127, Batch0140.tau1127, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322100 (by positivity) using 1 <;> norm_num)
        · have hs322102 : InSquare (9/160) (51/160) (1/160) tau := by
            convert childUL hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1129.sound htau (by
            simp only [Batch0141.cell1129, Batch0141.tau1129, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32210 | hy32210
        · have hs322101 : InSquare (11/160) (49/160) (1/160) tau := by
            convert childLR hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1128.sound htau (by
            simp only [Batch0141.cell1128, Batch0141.tau1128, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322101 (by positivity) using 1 <;> norm_num)
        · have hs322103 : InSquare (11/160) (51/160) (1/160) tau := by
            convert childUR hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1130.sound htau (by
            simp only [Batch0141.cell1130, Batch0141.tau1130, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322103 (by positivity) using 1 <;> norm_num)
    · have hs32212 : InSquare (1/16) (27/80) (1/80) tau := by
        convert childUL hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32212 | hx32212
      · rcases le_total tau.im (27/80 : ℝ) with hy32212 | hy32212
        · have hs322120 : InSquare (9/160) (53/160) (1/160) tau := by
            convert childLL hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0141.cell1135.sound htau (by
            simp only [Batch0141.cell1135, Batch0141.tau1135, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322120 (by positivity) using 1 <;> norm_num)
        · have hs322122 : InSquare (9/160) (11/32) (1/160) tau := by
            convert childUL hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0142.cell1137.sound htau (by
            simp only [Batch0142.cell1137, Batch0142.tau1137, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32212 | hy32212
        · have hs322121 : InSquare (11/160) (53/160) (1/160) tau := by
            convert childLR hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0142.cell1136.sound htau (by
            simp only [Batch0142.cell1136, Batch0142.tau1136, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322121 (by positivity) using 1 <;> norm_num)
        · have hs322123 : InSquare (11/160) (11/32) (1/160) tau := by
            convert childUR hs32212 hx32212 hy32212 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322123 | hx322123
          · rcases le_total tau.im (11/32 : ℝ) with hy322123 | hy322123
            · have hs3221230 : InSquare (21/320) (109/320) (1/320) tau := by
                convert childLL hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2224.sound htau (by
                simp only [Batch0278.cell2224, Batch0278.tau2224, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221230 (by positivity) using 1 <;> norm_num)
            · have hs3221232 : InSquare (21/320) (111/320) (1/320) tau := by
                convert childUL hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2226.sound htau (by
                simp only [Batch0278.cell2226, Batch0278.tau2226, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322123 | hy322123
            · have hs3221231 : InSquare (23/320) (109/320) (1/320) tau := by
                convert childLR hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2225.sound htau (by
                simp only [Batch0278.cell2225, Batch0278.tau2225, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221231 (by positivity) using 1 <;> norm_num)
            · have hs3221233 : InSquare (23/320) (111/320) (1/320) tau := by
                convert childUR hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2227.sound htau (by
                simp only [Batch0278.cell2227, Batch0278.tau2227, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3221 | hy3221
    · have hs32211 : InSquare (7/80) (5/16) (1/80) tau := by
        convert childLR hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32211 | hx32211
      · rcases le_total tau.im (5/16 : ℝ) with hy32211 | hy32211
        · have hs322110 : InSquare (13/160) (49/160) (1/160) tau := by
            convert childLL hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1131.sound htau (by
            simp only [Batch0141.cell1131, Batch0141.tau1131, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322110 (by positivity) using 1 <;> norm_num)
        · have hs322112 : InSquare (13/160) (51/160) (1/160) tau := by
            convert childUL hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1133.sound htau (by
            simp only [Batch0141.cell1133, Batch0141.tau1133, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32211 | hy32211
        · have hs322111 : InSquare (3/32) (49/160) (1/160) tau := by
            convert childLR hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1132.sound htau (by
            simp only [Batch0141.cell1132, Batch0141.tau1132, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322111 (by positivity) using 1 <;> norm_num)
        · have hs322113 : InSquare (3/32) (51/160) (1/160) tau := by
            convert childUR hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1134.sound htau (by
            simp only [Batch0141.cell1134, Batch0141.tau1134, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322113 (by positivity) using 1 <;> norm_num)
    · have hs32213 : InSquare (7/80) (27/80) (1/80) tau := by
        convert childUR hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32213 | hx32213
      · rcases le_total tau.im (27/80 : ℝ) with hy32213 | hy32213
        · have hs322130 : InSquare (13/160) (53/160) (1/160) tau := by
            convert childLL hs32213 hx32213 hy32213 using 1 <;> norm_num
          exact Batch0142.cell1138.sound htau (by
            simp only [Batch0142.cell1138, Batch0142.tau1138, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322130 (by positivity) using 1 <;> norm_num)
        · have hs322132 : InSquare (13/160) (11/32) (1/160) tau := by
            convert childUL hs32213 hx32213 hy32213 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322132 | hx322132
          · rcases le_total tau.im (11/32 : ℝ) with hy322132 | hy322132
            · have hs3221320 : InSquare (5/64) (109/320) (1/320) tau := by
                convert childLL hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2228.sound htau (by
                simp only [Batch0278.cell2228, Batch0278.tau2228, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221320 (by positivity) using 1 <;> norm_num)
            · have hs3221322 : InSquare (5/64) (111/320) (1/320) tau := by
                convert childUL hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2230.sound htau (by
                simp only [Batch0278.cell2230, Batch0278.tau2230, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322132 | hy322132
            · have hs3221321 : InSquare (27/320) (109/320) (1/320) tau := by
                convert childLR hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2229.sound htau (by
                simp only [Batch0278.cell2229, Batch0278.tau2229, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221321 (by positivity) using 1 <;> norm_num)
            · have hs3221323 : InSquare (27/320) (111/320) (1/320) tau := by
                convert childUR hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2231.sound htau (by
                simp only [Batch0278.cell2231, Batch0278.tau2231, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32213 | hy32213
        · have hs322131 : InSquare (3/32) (53/160) (1/160) tau := by
            convert childLR hs32213 hx32213 hy32213 using 1 <;> norm_num
          exact Batch0142.cell1139.sound htau (by
            simp only [Batch0142.cell1139, Batch0142.tau1139, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322131 (by positivity) using 1 <;> norm_num)
        · have hs322133 : InSquare (3/32) (11/32) (1/160) tau := by
            convert childUR hs32213 hx32213 hy32213 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322133 | hx322133
          · rcases le_total tau.im (11/32 : ℝ) with hy322133 | hy322133
            · have hs3221330 : InSquare (29/320) (109/320) (1/320) tau := by
                convert childLL hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2232.sound htau (by
                simp only [Batch0279.cell2232, Batch0279.tau2232, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221330 (by positivity) using 1 <;> norm_num)
            · have hs3221332 : InSquare (29/320) (111/320) (1/320) tau := by
                convert childUL hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2234.sound htau (by
                simp only [Batch0279.cell2234, Batch0279.tau2234, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322133 | hy322133
            · have hs3221331 : InSquare (31/320) (109/320) (1/320) tau := by
                convert childLR hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2233.sound htau (by
                simp only [Batch0279.cell2233, Batch0279.tau2233, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221331 (by positivity) using 1 <;> norm_num)
            · have hs3221333 : InSquare (31/320) (111/320) (1/320) tau := by
                convert childUR hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2235.sound htau (by
                simp only [Batch0279.cell2235, Batch0279.tau2235, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3222 | hx3222
  · rcases le_total tau.im (3/8 : ℝ) with hy3222 | hy3222
    · have hs32220 : InSquare (1/80) (29/80) (1/80) tau := by
        convert childLL hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32220 | hx32220
      · rcases le_total tau.im (29/80 : ℝ) with hy32220 | hy32220
        · have hs322200 : InSquare (1/160) (57/160) (1/160) tau := by
            convert childLL hs32220 hx32220 hy32220 using 1 <;> norm_num
          exact Batch0142.cell1140.sound htau (by
            simp only [Batch0142.cell1140, Batch0142.tau1140, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322200 (by positivity) using 1 <;> norm_num)
        · have hs322202 : InSquare (1/160) (59/160) (1/160) tau := by
            convert childUL hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322202 | hx322202
          · rcases le_total tau.im (59/160 : ℝ) with hy322202 | hy322202
            · have hs3222020 : InSquare (1/320) (117/320) (1/320) tau := by
                convert childLL hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2240.sound htau (by
                simp only [Batch0280.cell2240, Batch0280.tau2240, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222020 (by positivity) using 1 <;> norm_num)
            · have hs3222022 : InSquare (1/320) (119/320) (1/320) tau := by
                convert childUL hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2242.sound htau (by
                simp only [Batch0280.cell2242, Batch0280.tau2242, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322202 | hy322202
            · have hs3222021 : InSquare (3/320) (117/320) (1/320) tau := by
                convert childLR hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2241.sound htau (by
                simp only [Batch0280.cell2241, Batch0280.tau2241, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222021 (by positivity) using 1 <;> norm_num)
            · have hs3222023 : InSquare (3/320) (119/320) (1/320) tau := by
                convert childUR hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2243.sound htau (by
                simp only [Batch0280.cell2243, Batch0280.tau2243, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32220 | hy32220
        · have hs322201 : InSquare (3/160) (57/160) (1/160) tau := by
            convert childLR hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322201 | hx322201
          · rcases le_total tau.im (57/160 : ℝ) with hy322201 | hy322201
            · have hs3222010 : InSquare (1/64) (113/320) (1/320) tau := by
                convert childLL hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2236.sound htau (by
                simp only [Batch0279.cell2236, Batch0279.tau2236, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222010 (by positivity) using 1 <;> norm_num)
            · have hs3222012 : InSquare (1/64) (23/64) (1/320) tau := by
                convert childUL hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2238.sound htau (by
                simp only [Batch0279.cell2238, Batch0279.tau2238, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322201 | hy322201
            · have hs3222011 : InSquare (7/320) (113/320) (1/320) tau := by
                convert childLR hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2237.sound htau (by
                simp only [Batch0279.cell2237, Batch0279.tau2237, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222011 (by positivity) using 1 <;> norm_num)
            · have hs3222013 : InSquare (7/320) (23/64) (1/320) tau := by
                convert childUR hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2239.sound htau (by
                simp only [Batch0279.cell2239, Batch0279.tau2239, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222013 (by positivity) using 1 <;> norm_num)
        · have hs322203 : InSquare (3/160) (59/160) (1/160) tau := by
            convert childUR hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322203 | hx322203
          · rcases le_total tau.im (59/160 : ℝ) with hy322203 | hy322203
            · have hs3222030 : InSquare (1/64) (117/320) (1/320) tau := by
                convert childLL hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2244.sound htau (by
                simp only [Batch0280.cell2244, Batch0280.tau2244, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222030 (by positivity) using 1 <;> norm_num)
            · have hs3222032 : InSquare (1/64) (119/320) (1/320) tau := by
                convert childUL hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2246.sound htau (by
                simp only [Batch0280.cell2246, Batch0280.tau2246, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322203 | hy322203
            · have hs3222031 : InSquare (7/320) (117/320) (1/320) tau := by
                convert childLR hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2245.sound htau (by
                simp only [Batch0280.cell2245, Batch0280.tau2245, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222031 (by positivity) using 1 <;> norm_num)
            · have hs3222033 : InSquare (7/320) (119/320) (1/320) tau := by
                convert childUR hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2247.sound htau (by
                simp only [Batch0280.cell2247, Batch0280.tau2247, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222033 (by positivity) using 1 <;> norm_num)
    · have hs32222 : InSquare (1/80) (31/80) (1/80) tau := by
        convert childUL hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32222 | hx32222
      · rcases le_total tau.im (31/80 : ℝ) with hy32222 | hy32222
        · have hs322220 : InSquare (1/160) (61/160) (1/160) tau := by
            convert childLL hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322220 | hx322220
          · rcases le_total tau.im (61/160 : ℝ) with hy322220 | hy322220
            · have hs3222200 : InSquare (1/320) (121/320) (1/320) tau := by
                convert childLL hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2264.sound htau (by
                simp only [Batch0283.cell2264, Batch0283.tau2264, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222200 (by positivity) using 1 <;> norm_num)
            · have hs3222202 : InSquare (1/320) (123/320) (1/320) tau := by
                convert childUL hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2266.sound htau (by
                simp only [Batch0283.cell2266, Batch0283.tau2266, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322220 | hy322220
            · have hs3222201 : InSquare (3/320) (121/320) (1/320) tau := by
                convert childLR hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2265.sound htau (by
                simp only [Batch0283.cell2265, Batch0283.tau2265, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222201 (by positivity) using 1 <;> norm_num)
            · have hs3222203 : InSquare (3/320) (123/320) (1/320) tau := by
                convert childUR hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2267.sound htau (by
                simp only [Batch0283.cell2267, Batch0283.tau2267, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222203 (by positivity) using 1 <;> norm_num)
        · have hs322222 : InSquare (1/160) (63/160) (1/160) tau := by
            convert childUL hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322222 | hx322222
          · rcases le_total tau.im (63/160 : ℝ) with hy322222 | hy322222
            · have hs3222220 : InSquare (1/320) (25/64) (1/320) tau := by
                convert childLL hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx3222220 | hx3222220
              · rcases le_total tau.im (25/64 : ℝ) with hy3222220 | hy3222220
                · have hs32222200 : InSquare (1/640) (249/640) (1/640) tau := by
                    convert childLL hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3524.sound htau (by
                    simp only [Batch0440.cell3524, Batch0440.tau3524, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222200 (by positivity) using 1 <;> norm_num)
                · have hs32222202 : InSquare (1/640) (251/640) (1/640) tau := by
                    convert childUL hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3526.sound htau (by
                    simp only [Batch0440.cell3526, Batch0440.tau3526, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222220 | hy3222220
                · have hs32222201 : InSquare (3/640) (249/640) (1/640) tau := by
                    convert childLR hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3525.sound htau (by
                    simp only [Batch0440.cell3525, Batch0440.tau3525, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222201 (by positivity) using 1 <;> norm_num)
                · have hs32222203 : InSquare (3/640) (251/640) (1/640) tau := by
                    convert childUR hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3527.sound htau (by
                    simp only [Batch0440.cell3527, Batch0440.tau3527, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222203 (by positivity) using 1 <;> norm_num)
            · have hs3222222 : InSquare (1/320) (127/320) (1/320) tau := by
                convert childUL hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx3222222 | hx3222222
              · rcases le_total tau.im (127/320 : ℝ) with hy3222222 | hy3222222
                · have hs32222220 : InSquare (1/640) (253/640) (1/640) tau := by
                    convert childLL hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3532.sound htau (by
                    simp only [Batch0441.cell3532, Batch0441.tau3532, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222220 (by positivity) using 1 <;> norm_num)
                · have hs32222222 : InSquare (1/640) (51/128) (1/640) tau := by
                    convert childUL hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3534.sound htau (by
                    simp only [Batch0441.cell3534, Batch0441.tau3534, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222222 | hy3222222
                · have hs32222221 : InSquare (3/640) (253/640) (1/640) tau := by
                    convert childLR hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3533.sound htau (by
                    simp only [Batch0441.cell3533, Batch0441.tau3533, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222221 (by positivity) using 1 <;> norm_num)
                · have hs32222223 : InSquare (3/640) (51/128) (1/640) tau := by
                    convert childUR hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3535.sound htau (by
                    simp only [Batch0441.cell3535, Batch0441.tau3535, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322222 | hy322222
            · have hs3222221 : InSquare (3/320) (25/64) (1/320) tau := by
                convert childLR hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx3222221 | hx3222221
              · rcases le_total tau.im (25/64 : ℝ) with hy3222221 | hy3222221
                · have hs32222210 : InSquare (1/128) (249/640) (1/640) tau := by
                    convert childLL hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3528.sound htau (by
                    simp only [Batch0441.cell3528, Batch0441.tau3528, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222210 (by positivity) using 1 <;> norm_num)
                · have hs32222212 : InSquare (1/128) (251/640) (1/640) tau := by
                    convert childUL hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3530.sound htau (by
                    simp only [Batch0441.cell3530, Batch0441.tau3530, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222221 | hy3222221
                · have hs32222211 : InSquare (7/640) (249/640) (1/640) tau := by
                    convert childLR hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3529.sound htau (by
                    simp only [Batch0441.cell3529, Batch0441.tau3529, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222211 (by positivity) using 1 <;> norm_num)
                · have hs32222213 : InSquare (7/640) (251/640) (1/640) tau := by
                    convert childUR hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3531.sound htau (by
                    simp only [Batch0441.cell3531, Batch0441.tau3531, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222213 (by positivity) using 1 <;> norm_num)
            · have hs3222223 : InSquare (3/320) (127/320) (1/320) tau := by
                convert childUR hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx3222223 | hx3222223
              · rcases le_total tau.im (127/320 : ℝ) with hy3222223 | hy3222223
                · have hs32222230 : InSquare (1/128) (253/640) (1/640) tau := by
                    convert childLL hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3536.sound htau (by
                    simp only [Batch0442.cell3536, Batch0442.tau3536, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222230 (by positivity) using 1 <;> norm_num)
                · have hs32222232 : InSquare (1/128) (51/128) (1/640) tau := by
                    convert childUL hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3538.sound htau (by
                    simp only [Batch0442.cell3538, Batch0442.tau3538, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222223 | hy3222223
                · have hs32222231 : InSquare (7/640) (253/640) (1/640) tau := by
                    convert childLR hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3537.sound htau (by
                    simp only [Batch0442.cell3537, Batch0442.tau3537, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222231 (by positivity) using 1 <;> norm_num)
                · have hs32222233 : InSquare (7/640) (51/128) (1/640) tau := by
                    convert childUR hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3539.sound htau (by
                    simp only [Batch0442.cell3539, Batch0442.tau3539, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy32222 | hy32222
        · have hs322221 : InSquare (3/160) (61/160) (1/160) tau := by
            convert childLR hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322221 | hx322221
          · rcases le_total tau.im (61/160 : ℝ) with hy322221 | hy322221
            · have hs3222210 : InSquare (1/64) (121/320) (1/320) tau := by
                convert childLL hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2268.sound htau (by
                simp only [Batch0283.cell2268, Batch0283.tau2268, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222210 (by positivity) using 1 <;> norm_num)
            · have hs3222212 : InSquare (1/64) (123/320) (1/320) tau := by
                convert childUL hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2270.sound htau (by
                simp only [Batch0283.cell2270, Batch0283.tau2270, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322221 | hy322221
            · have hs3222211 : InSquare (7/320) (121/320) (1/320) tau := by
                convert childLR hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2269.sound htau (by
                simp only [Batch0283.cell2269, Batch0283.tau2269, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222211 (by positivity) using 1 <;> norm_num)
            · have hs3222213 : InSquare (7/320) (123/320) (1/320) tau := by
                convert childUR hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2271.sound htau (by
                simp only [Batch0283.cell2271, Batch0283.tau2271, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222213 (by positivity) using 1 <;> norm_num)
        · have hs322223 : InSquare (3/160) (63/160) (1/160) tau := by
            convert childUR hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322223 | hx322223
          · rcases le_total tau.im (63/160 : ℝ) with hy322223 | hy322223
            · have hs3222230 : InSquare (1/64) (25/64) (1/320) tau := by
                convert childLL hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx3222230 | hx3222230
              · rcases le_total tau.im (25/64 : ℝ) with hy3222230 | hy3222230
                · have hs32222300 : InSquare (9/640) (249/640) (1/640) tau := by
                    convert childLL hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3540.sound htau (by
                    simp only [Batch0442.cell3540, Batch0442.tau3540, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222300 (by positivity) using 1 <;> norm_num)
                · have hs32222302 : InSquare (9/640) (251/640) (1/640) tau := by
                    convert childUL hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3542.sound htau (by
                    simp only [Batch0442.cell3542, Batch0442.tau3542, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222230 | hy3222230
                · have hs32222301 : InSquare (11/640) (249/640) (1/640) tau := by
                    convert childLR hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3541.sound htau (by
                    simp only [Batch0442.cell3541, Batch0442.tau3541, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222301 (by positivity) using 1 <;> norm_num)
                · have hs32222303 : InSquare (11/640) (251/640) (1/640) tau := by
                    convert childUR hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3543.sound htau (by
                    simp only [Batch0442.cell3543, Batch0442.tau3543, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222303 (by positivity) using 1 <;> norm_num)
            · have hs3222232 : InSquare (1/64) (127/320) (1/320) tau := by
                convert childUL hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx3222232 | hx3222232
              · rcases le_total tau.im (127/320 : ℝ) with hy3222232 | hy3222232
                · have hs32222320 : InSquare (9/640) (253/640) (1/640) tau := by
                    convert childLL hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3548.sound htau (by
                    simp only [Batch0443.cell3548, Batch0443.tau3548, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222320 (by positivity) using 1 <;> norm_num)
                · have hs32222322 : InSquare (9/640) (51/128) (1/640) tau := by
                    convert childUL hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3550.sound htau (by
                    simp only [Batch0443.cell3550, Batch0443.tau3550, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222232 | hy3222232
                · have hs32222321 : InSquare (11/640) (253/640) (1/640) tau := by
                    convert childLR hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3549.sound htau (by
                    simp only [Batch0443.cell3549, Batch0443.tau3549, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222321 (by positivity) using 1 <;> norm_num)
                · have hs32222323 : InSquare (11/640) (51/128) (1/640) tau := by
                    convert childUR hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3551.sound htau (by
                    simp only [Batch0443.cell3551, Batch0443.tau3551, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322223 | hy322223
            · have hs3222231 : InSquare (7/320) (25/64) (1/320) tau := by
                convert childLR hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx3222231 | hx3222231
              · rcases le_total tau.im (25/64 : ℝ) with hy3222231 | hy3222231
                · have hs32222310 : InSquare (13/640) (249/640) (1/640) tau := by
                    convert childLL hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3544.sound htau (by
                    simp only [Batch0443.cell3544, Batch0443.tau3544, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222310 (by positivity) using 1 <;> norm_num)
                · have hs32222312 : InSquare (13/640) (251/640) (1/640) tau := by
                    convert childUL hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3546.sound htau (by
                    simp only [Batch0443.cell3546, Batch0443.tau3546, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222231 | hy3222231
                · have hs32222311 : InSquare (3/128) (249/640) (1/640) tau := by
                    convert childLR hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3545.sound htau (by
                    simp only [Batch0443.cell3545, Batch0443.tau3545, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222311 (by positivity) using 1 <;> norm_num)
                · have hs32222313 : InSquare (3/128) (251/640) (1/640) tau := by
                    convert childUR hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3547.sound htau (by
                    simp only [Batch0443.cell3547, Batch0443.tau3547, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222313 (by positivity) using 1 <;> norm_num)
            · have hs3222233 : InSquare (7/320) (127/320) (1/320) tau := by
                convert childUR hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx3222233 | hx3222233
              · rcases le_total tau.im (127/320 : ℝ) with hy3222233 | hy3222233
                · have hs32222330 : InSquare (13/640) (253/640) (1/640) tau := by
                    convert childLL hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3552.sound htau (by
                    simp only [Batch0444.cell3552, Batch0444.tau3552, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222330 (by positivity) using 1 <;> norm_num)
                · have hs32222332 : InSquare (13/640) (51/128) (1/640) tau := by
                    convert childUL hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3554.sound htau (by
                    simp only [Batch0444.cell3554, Batch0444.tau3554, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222233 | hy3222233
                · have hs32222331 : InSquare (3/128) (253/640) (1/640) tau := by
                    convert childLR hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3553.sound htau (by
                    simp only [Batch0444.cell3553, Batch0444.tau3553, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222331 (by positivity) using 1 <;> norm_num)
                · have hs32222333 : InSquare (3/128) (51/128) (1/640) tau := by
                    convert childUR hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3555.sound htau (by
                    simp only [Batch0444.cell3555, Batch0444.tau3555, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/8 : ℝ) with hy3222 | hy3222
    · have hs32221 : InSquare (3/80) (29/80) (1/80) tau := by
        convert childLR hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32221 | hx32221
      · rcases le_total tau.im (29/80 : ℝ) with hy32221 | hy32221
        · have hs322210 : InSquare (1/32) (57/160) (1/160) tau := by
            convert childLL hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322210 | hx322210
          · rcases le_total tau.im (57/160 : ℝ) with hy322210 | hy322210
            · have hs3222100 : InSquare (9/320) (113/320) (1/320) tau := by
                convert childLL hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2248.sound htau (by
                simp only [Batch0281.cell2248, Batch0281.tau2248, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222100 (by positivity) using 1 <;> norm_num)
            · have hs3222102 : InSquare (9/320) (23/64) (1/320) tau := by
                convert childUL hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2250.sound htau (by
                simp only [Batch0281.cell2250, Batch0281.tau2250, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322210 | hy322210
            · have hs3222101 : InSquare (11/320) (113/320) (1/320) tau := by
                convert childLR hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2249.sound htau (by
                simp only [Batch0281.cell2249, Batch0281.tau2249, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222101 (by positivity) using 1 <;> norm_num)
            · have hs3222103 : InSquare (11/320) (23/64) (1/320) tau := by
                convert childUR hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2251.sound htau (by
                simp only [Batch0281.cell2251, Batch0281.tau2251, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222103 (by positivity) using 1 <;> norm_num)
        · have hs322212 : InSquare (1/32) (59/160) (1/160) tau := by
            convert childUL hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322212 | hx322212
          · rcases le_total tau.im (59/160 : ℝ) with hy322212 | hy322212
            · have hs3222120 : InSquare (9/320) (117/320) (1/320) tau := by
                convert childLL hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2256.sound htau (by
                simp only [Batch0282.cell2256, Batch0282.tau2256, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222120 (by positivity) using 1 <;> norm_num)
            · have hs3222122 : InSquare (9/320) (119/320) (1/320) tau := by
                convert childUL hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2258.sound htau (by
                simp only [Batch0282.cell2258, Batch0282.tau2258, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322212 | hy322212
            · have hs3222121 : InSquare (11/320) (117/320) (1/320) tau := by
                convert childLR hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2257.sound htau (by
                simp only [Batch0282.cell2257, Batch0282.tau2257, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222121 (by positivity) using 1 <;> norm_num)
            · have hs3222123 : InSquare (11/320) (119/320) (1/320) tau := by
                convert childUR hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2259.sound htau (by
                simp only [Batch0282.cell2259, Batch0282.tau2259, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32221 | hy32221
        · have hs322211 : InSquare (7/160) (57/160) (1/160) tau := by
            convert childLR hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322211 | hx322211
          · rcases le_total tau.im (57/160 : ℝ) with hy322211 | hy322211
            · have hs3222110 : InSquare (13/320) (113/320) (1/320) tau := by
                convert childLL hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2252.sound htau (by
                simp only [Batch0281.cell2252, Batch0281.tau2252, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222110 (by positivity) using 1 <;> norm_num)
            · have hs3222112 : InSquare (13/320) (23/64) (1/320) tau := by
                convert childUL hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2254.sound htau (by
                simp only [Batch0281.cell2254, Batch0281.tau2254, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322211 | hy322211
            · have hs3222111 : InSquare (3/64) (113/320) (1/320) tau := by
                convert childLR hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2253.sound htau (by
                simp only [Batch0281.cell2253, Batch0281.tau2253, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222111 (by positivity) using 1 <;> norm_num)
            · have hs3222113 : InSquare (3/64) (23/64) (1/320) tau := by
                convert childUR hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2255.sound htau (by
                simp only [Batch0281.cell2255, Batch0281.tau2255, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222113 (by positivity) using 1 <;> norm_num)
        · have hs322213 : InSquare (7/160) (59/160) (1/160) tau := by
            convert childUR hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322213 | hx322213
          · rcases le_total tau.im (59/160 : ℝ) with hy322213 | hy322213
            · have hs3222130 : InSquare (13/320) (117/320) (1/320) tau := by
                convert childLL hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2260.sound htau (by
                simp only [Batch0282.cell2260, Batch0282.tau2260, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222130 (by positivity) using 1 <;> norm_num)
            · have hs3222132 : InSquare (13/320) (119/320) (1/320) tau := by
                convert childUL hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2262.sound htau (by
                simp only [Batch0282.cell2262, Batch0282.tau2262, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322213 | hy322213
            · have hs3222131 : InSquare (3/64) (117/320) (1/320) tau := by
                convert childLR hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2261.sound htau (by
                simp only [Batch0282.cell2261, Batch0282.tau2261, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222131 (by positivity) using 1 <;> norm_num)
            · have hs3222133 : InSquare (3/64) (119/320) (1/320) tau := by
                convert childUR hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2263.sound htau (by
                simp only [Batch0282.cell2263, Batch0282.tau2263, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222133 (by positivity) using 1 <;> norm_num)
    · have hs32223 : InSquare (3/80) (31/80) (1/80) tau := by
        convert childUR hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32223 | hx32223
      · rcases le_total tau.im (31/80 : ℝ) with hy32223 | hy32223
        · have hs322230 : InSquare (1/32) (61/160) (1/160) tau := by
            convert childLL hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322230 | hx322230
          · rcases le_total tau.im (61/160 : ℝ) with hy322230 | hy322230
            · have hs3222300 : InSquare (9/320) (121/320) (1/320) tau := by
                convert childLL hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2272.sound htau (by
                simp only [Batch0284.cell2272, Batch0284.tau2272, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222300 (by positivity) using 1 <;> norm_num)
            · have hs3222302 : InSquare (9/320) (123/320) (1/320) tau := by
                convert childUL hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2274.sound htau (by
                simp only [Batch0284.cell2274, Batch0284.tau2274, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322230 | hy322230
            · have hs3222301 : InSquare (11/320) (121/320) (1/320) tau := by
                convert childLR hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2273.sound htau (by
                simp only [Batch0284.cell2273, Batch0284.tau2273, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222301 (by positivity) using 1 <;> norm_num)
            · have hs3222303 : InSquare (11/320) (123/320) (1/320) tau := by
                convert childUR hs322230 hx322230 hy322230 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222303 | hx3222303
              · rcases le_total tau.im (123/320 : ℝ) with hy3222303 | hy3222303
                · have hs32223030 : InSquare (21/640) (49/128) (1/640) tau := by
                    convert childLL hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3556.sound htau (by
                    simp only [Batch0444.cell3556, Batch0444.tau3556, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223030 (by positivity) using 1 <;> norm_num)
                · have hs32223032 : InSquare (21/640) (247/640) (1/640) tau := by
                    convert childUL hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3558.sound htau (by
                    simp only [Batch0444.cell3558, Batch0444.tau3558, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222303 | hy3222303
                · have hs32223031 : InSquare (23/640) (49/128) (1/640) tau := by
                    convert childLR hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3557.sound htau (by
                    simp only [Batch0444.cell3557, Batch0444.tau3557, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223031 (by positivity) using 1 <;> norm_num)
                · have hs32223033 : InSquare (23/640) (247/640) (1/640) tau := by
                    convert childUR hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3559.sound htau (by
                    simp only [Batch0444.cell3559, Batch0444.tau3559, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223033 (by positivity) using 1 <;> norm_num)
        · have hs322232 : InSquare (1/32) (63/160) (1/160) tau := by
            convert childUL hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322232 | hx322232
          · rcases le_total tau.im (63/160 : ℝ) with hy322232 | hy322232
            · have hs3222320 : InSquare (9/320) (25/64) (1/320) tau := by
                convert childLL hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx3222320 | hx3222320
              · rcases le_total tau.im (25/64 : ℝ) with hy3222320 | hy3222320
                · have hs32223200 : InSquare (17/640) (249/640) (1/640) tau := by
                    convert childLL hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3568.sound htau (by
                    simp only [Batch0446.cell3568, Batch0446.tau3568, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223200 (by positivity) using 1 <;> norm_num)
                · have hs32223202 : InSquare (17/640) (251/640) (1/640) tau := by
                    convert childUL hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3570.sound htau (by
                    simp only [Batch0446.cell3570, Batch0446.tau3570, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222320 | hy3222320
                · have hs32223201 : InSquare (19/640) (249/640) (1/640) tau := by
                    convert childLR hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3569.sound htau (by
                    simp only [Batch0446.cell3569, Batch0446.tau3569, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223201 (by positivity) using 1 <;> norm_num)
                · have hs32223203 : InSquare (19/640) (251/640) (1/640) tau := by
                    convert childUR hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3571.sound htau (by
                    simp only [Batch0446.cell3571, Batch0446.tau3571, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223203 (by positivity) using 1 <;> norm_num)
            · have hs3222322 : InSquare (9/320) (127/320) (1/320) tau := by
                convert childUL hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx3222322 | hx3222322
              · rcases le_total tau.im (127/320 : ℝ) with hy3222322 | hy3222322
                · have hs32223220 : InSquare (17/640) (253/640) (1/640) tau := by
                    convert childLL hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3576.sound htau (by
                    simp only [Batch0447.cell3576, Batch0447.tau3576, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223220 (by positivity) using 1 <;> norm_num)
                · have hs32223222 : InSquare (17/640) (51/128) (1/640) tau := by
                    convert childUL hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3578.sound htau (by
                    simp only [Batch0447.cell3578, Batch0447.tau3578, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222322 | hy3222322
                · have hs32223221 : InSquare (19/640) (253/640) (1/640) tau := by
                    convert childLR hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3577.sound htau (by
                    simp only [Batch0447.cell3577, Batch0447.tau3577, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223221 (by positivity) using 1 <;> norm_num)
                · have hs32223223 : InSquare (19/640) (51/128) (1/640) tau := by
                    convert childUR hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3579.sound htau (by
                    simp only [Batch0447.cell3579, Batch0447.tau3579, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322232 | hy322232
            · have hs3222321 : InSquare (11/320) (25/64) (1/320) tau := by
                convert childLR hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222321 | hx3222321
              · rcases le_total tau.im (25/64 : ℝ) with hy3222321 | hy3222321
                · have hs32223210 : InSquare (21/640) (249/640) (1/640) tau := by
                    convert childLL hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3572.sound htau (by
                    simp only [Batch0446.cell3572, Batch0446.tau3572, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223210 (by positivity) using 1 <;> norm_num)
                · have hs32223212 : InSquare (21/640) (251/640) (1/640) tau := by
                    convert childUL hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3574.sound htau (by
                    simp only [Batch0446.cell3574, Batch0446.tau3574, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222321 | hy3222321
                · have hs32223211 : InSquare (23/640) (249/640) (1/640) tau := by
                    convert childLR hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3573.sound htau (by
                    simp only [Batch0446.cell3573, Batch0446.tau3573, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223211 (by positivity) using 1 <;> norm_num)
                · have hs32223213 : InSquare (23/640) (251/640) (1/640) tau := by
                    convert childUR hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3575.sound htau (by
                    simp only [Batch0446.cell3575, Batch0446.tau3575, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223213 (by positivity) using 1 <;> norm_num)
            · have hs3222323 : InSquare (11/320) (127/320) (1/320) tau := by
                convert childUR hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222323 | hx3222323
              · rcases le_total tau.im (127/320 : ℝ) with hy3222323 | hy3222323
                · have hs32223230 : InSquare (21/640) (253/640) (1/640) tau := by
                    convert childLL hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3580.sound htau (by
                    simp only [Batch0447.cell3580, Batch0447.tau3580, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223230 (by positivity) using 1 <;> norm_num)
                · have hs32223232 : InSquare (21/640) (51/128) (1/640) tau := by
                    convert childUL hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3582.sound htau (by
                    simp only [Batch0447.cell3582, Batch0447.tau3582, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222323 | hy3222323
                · have hs32223231 : InSquare (23/640) (253/640) (1/640) tau := by
                    convert childLR hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3581.sound htau (by
                    simp only [Batch0447.cell3581, Batch0447.tau3581, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223231 (by positivity) using 1 <;> norm_num)
                · have hs32223233 : InSquare (23/640) (51/128) (1/640) tau := by
                    convert childUR hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3583.sound htau (by
                    simp only [Batch0447.cell3583, Batch0447.tau3583, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy32223 | hy32223
        · have hs322231 : InSquare (7/160) (61/160) (1/160) tau := by
            convert childLR hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322231 | hx322231
          · rcases le_total tau.im (61/160 : ℝ) with hy322231 | hy322231
            · have hs3222310 : InSquare (13/320) (121/320) (1/320) tau := by
                convert childLL hs322231 hx322231 hy322231 using 1 <;> norm_num
              exact Batch0284.cell2275.sound htau (by
                simp only [Batch0284.cell2275, Batch0284.tau2275, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222310 (by positivity) using 1 <;> norm_num)
            · have hs3222312 : InSquare (13/320) (123/320) (1/320) tau := by
                convert childUL hs322231 hx322231 hy322231 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222312 | hx3222312
              · rcases le_total tau.im (123/320 : ℝ) with hy3222312 | hy3222312
                · have hs32223120 : InSquare (5/128) (49/128) (1/640) tau := by
                    convert childLL hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3560.sound htau (by
                    simp only [Batch0445.cell3560, Batch0445.tau3560, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223120 (by positivity) using 1 <;> norm_num)
                · have hs32223122 : InSquare (5/128) (247/640) (1/640) tau := by
                    convert childUL hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3562.sound htau (by
                    simp only [Batch0445.cell3562, Batch0445.tau3562, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222312 | hy3222312
                · have hs32223121 : InSquare (27/640) (49/128) (1/640) tau := by
                    convert childLR hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3561.sound htau (by
                    simp only [Batch0445.cell3561, Batch0445.tau3561, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223121 (by positivity) using 1 <;> norm_num)
                · have hs32223123 : InSquare (27/640) (247/640) (1/640) tau := by
                    convert childUR hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3563.sound htau (by
                    simp only [Batch0445.cell3563, Batch0445.tau3563, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322231 | hy322231
            · have hs3222311 : InSquare (3/64) (121/320) (1/320) tau := by
                convert childLR hs322231 hx322231 hy322231 using 1 <;> norm_num
              exact Batch0284.cell2276.sound htau (by
                simp only [Batch0284.cell2276, Batch0284.tau2276, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222311 (by positivity) using 1 <;> norm_num)
            · have hs3222313 : InSquare (3/64) (123/320) (1/320) tau := by
                convert childUR hs322231 hx322231 hy322231 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222313 | hx3222313
              · rcases le_total tau.im (123/320 : ℝ) with hy3222313 | hy3222313
                · have hs32223130 : InSquare (29/640) (49/128) (1/640) tau := by
                    convert childLL hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3564.sound htau (by
                    simp only [Batch0445.cell3564, Batch0445.tau3564, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223130 (by positivity) using 1 <;> norm_num)
                · have hs32223132 : InSquare (29/640) (247/640) (1/640) tau := by
                    convert childUL hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3566.sound htau (by
                    simp only [Batch0445.cell3566, Batch0445.tau3566, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222313 | hy3222313
                · have hs32223131 : InSquare (31/640) (49/128) (1/640) tau := by
                    convert childLR hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3565.sound htau (by
                    simp only [Batch0445.cell3565, Batch0445.tau3565, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223131 (by positivity) using 1 <;> norm_num)
                · have hs32223133 : InSquare (31/640) (247/640) (1/640) tau := by
                    convert childUR hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3567.sound htau (by
                    simp only [Batch0445.cell3567, Batch0445.tau3567, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223133 (by positivity) using 1 <;> norm_num)
        · have hs322233 : InSquare (7/160) (63/160) (1/160) tau := by
            convert childUR hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322233 | hx322233
          · rcases le_total tau.im (63/160 : ℝ) with hy322233 | hy322233
            · have hs3222330 : InSquare (13/320) (25/64) (1/320) tau := by
                convert childLL hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222330 | hx3222330
              · rcases le_total tau.im (25/64 : ℝ) with hy3222330 | hy3222330
                · have hs32223300 : InSquare (5/128) (249/640) (1/640) tau := by
                    convert childLL hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3584.sound htau (by
                    simp only [Batch0448.cell3584, Batch0448.tau3584, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223300 (by positivity) using 1 <;> norm_num)
                · have hs32223302 : InSquare (5/128) (251/640) (1/640) tau := by
                    convert childUL hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3586.sound htau (by
                    simp only [Batch0448.cell3586, Batch0448.tau3586, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222330 | hy3222330
                · have hs32223301 : InSquare (27/640) (249/640) (1/640) tau := by
                    convert childLR hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3585.sound htau (by
                    simp only [Batch0448.cell3585, Batch0448.tau3585, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223301 (by positivity) using 1 <;> norm_num)
                · have hs32223303 : InSquare (27/640) (251/640) (1/640) tau := by
                    convert childUR hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3587.sound htau (by
                    simp only [Batch0448.cell3587, Batch0448.tau3587, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223303 (by positivity) using 1 <;> norm_num)
            · have hs3222332 : InSquare (13/320) (127/320) (1/320) tau := by
                convert childUL hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222332 | hx3222332
              · rcases le_total tau.im (127/320 : ℝ) with hy3222332 | hy3222332
                · have hs32223320 : InSquare (5/128) (253/640) (1/640) tau := by
                    convert childLL hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3592.sound htau (by
                    simp only [Batch0449.cell3592, Batch0449.tau3592, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223320 (by positivity) using 1 <;> norm_num)
                · have hs32223322 : InSquare (5/128) (51/128) (1/640) tau := by
                    convert childUL hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3594.sound htau (by
                    simp only [Batch0449.cell3594, Batch0449.tau3594, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222332 | hy3222332
                · have hs32223321 : InSquare (27/640) (253/640) (1/640) tau := by
                    convert childLR hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3593.sound htau (by
                    simp only [Batch0449.cell3593, Batch0449.tau3593, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223321 (by positivity) using 1 <;> norm_num)
                · have hs32223323 : InSquare (27/640) (51/128) (1/640) tau := by
                    convert childUR hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3595.sound htau (by
                    simp only [Batch0449.cell3595, Batch0449.tau3595, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322233 | hy322233
            · have hs3222331 : InSquare (3/64) (25/64) (1/320) tau := by
                convert childLR hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222331 | hx3222331
              · rcases le_total tau.im (25/64 : ℝ) with hy3222331 | hy3222331
                · have hs32223310 : InSquare (29/640) (249/640) (1/640) tau := by
                    convert childLL hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3588.sound htau (by
                    simp only [Batch0448.cell3588, Batch0448.tau3588, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223310 (by positivity) using 1 <;> norm_num)
                · have hs32223312 : InSquare (29/640) (251/640) (1/640) tau := by
                    convert childUL hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3590.sound htau (by
                    simp only [Batch0448.cell3590, Batch0448.tau3590, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222331 | hy3222331
                · have hs32223311 : InSquare (31/640) (249/640) (1/640) tau := by
                    convert childLR hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3589.sound htau (by
                    simp only [Batch0448.cell3589, Batch0448.tau3589, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223311 (by positivity) using 1 <;> norm_num)
                · have hs32223313 : InSquare (31/640) (251/640) (1/640) tau := by
                    convert childUR hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3591.sound htau (by
                    simp only [Batch0448.cell3591, Batch0448.tau3591, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223313 (by positivity) using 1 <;> norm_num)
            · have hs3222333 : InSquare (3/64) (127/320) (1/320) tau := by
                convert childUR hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222333 | hx3222333
              · rcases le_total tau.im (127/320 : ℝ) with hy3222333 | hy3222333
                · have hs32223330 : InSquare (29/640) (253/640) (1/640) tau := by
                    convert childLL hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3596.sound htau (by
                    simp only [Batch0449.cell3596, Batch0449.tau3596, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223330 (by positivity) using 1 <;> norm_num)
                · have hs32223332 : InSquare (29/640) (51/128) (1/640) tau := by
                    convert childUL hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3598.sound htau (by
                    simp only [Batch0449.cell3598, Batch0449.tau3598, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222333 | hy3222333
                · have hs32223331 : InSquare (31/640) (253/640) (1/640) tau := by
                    convert childLR hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3597.sound htau (by
                    simp only [Batch0449.cell3597, Batch0449.tau3597, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223331 (by positivity) using 1 <;> norm_num)
                · have hs32223333 : InSquare (31/640) (51/128) (1/640) tau := by
                    convert childUR hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3599.sound htau (by
                    simp only [Batch0449.cell3599, Batch0449.tau3599, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222

end


