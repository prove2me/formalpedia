-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1132__16
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage1132__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:14:32.113912+00:00
-- url     : https://prove2.me/theorems/55e1b389-8d66-45b3-a49e-4f15ce6573bb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132 (+15 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132 (+15 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132 (+15 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132 (+15 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1132 (+15 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1201, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1210, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1211, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1213, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1300, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1301, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1302, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1303, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1310, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1311, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1312, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1313, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1320, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1321, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage1323).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0232
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0234
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0018
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0093
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0094
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_113210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/160) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (-37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (103/320) (-79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (-15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (-73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1132 | hx1132
  · rcases le_total tau.im (-9/40 : ℝ) with hy1132 | hy1132
    · have hs11320 : InSquare (5/16) (-19/80) (1/80) tau := by
        convert childLL hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11320 | hx11320
      · rcases le_total tau.im (-19/80 : ℝ) with hy11320 | hy11320
        · have hs113200 : InSquare (49/160) (-39/160) (1/160) tau := by
            convert childLL hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113200 | hx113200
          · rcases le_total tau.im (-39/160 : ℝ) with hy113200 | hy113200
            · have hs1132000 : InSquare (97/320) (-79/320) (1/320) tau := by
                convert childLL hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1860.sound htau (by
                simp only [Batch0232.cell1860, Batch0232.tau1860, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132000 (by positivity) using 1 <;> norm_num)
            · have hs1132002 : InSquare (97/320) (-77/320) (1/320) tau := by
                convert childUL hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1862.sound htau (by
                simp only [Batch0232.cell1862, Batch0232.tau1862, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy113200 | hy113200
            · have hs1132001 : InSquare (99/320) (-79/320) (1/320) tau := by
                convert childLR hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1861.sound htau (by
                simp only [Batch0232.cell1861, Batch0232.tau1861, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132001 (by positivity) using 1 <;> norm_num)
            · have hs1132003 : InSquare (99/320) (-77/320) (1/320) tau := by
                convert childUR hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1863.sound htau (by
                simp only [Batch0232.cell1863, Batch0232.tau1863, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132003 (by positivity) using 1 <;> norm_num)
        · have hs113202 : InSquare (49/160) (-37/160) (1/160) tau := by
            convert childUL hs11320 hx11320 hy11320 using 1 <;> norm_num
          exact Batch0086.cell0689.sound htau (by
            simp only [Batch0086.cell0689, Batch0086.tau0689, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11320 | hy11320
        · have hs113201 : InSquare (51/160) (-39/160) (1/160) tau := by
            convert childLR hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx113201 | hx113201
          · rcases le_total tau.im (-39/160 : ℝ) with hy113201 | hy113201
            · have hs1132010 : InSquare (101/320) (-79/320) (1/320) tau := by
                convert childLL hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1864.sound htau (by
                simp only [Batch0233.cell1864, Batch0233.tau1864, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132010 (by positivity) using 1 <;> norm_num)
            · have hs1132012 : InSquare (101/320) (-77/320) (1/320) tau := by
                convert childUL hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1865.sound htau (by
                simp only [Batch0233.cell1865, Batch0233.tau1865, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy113201 | hy113201
            · have hs1132011 : InSquare (103/320) (-79/320) (1/320) tau := by
                convert childLR hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact (outside_1132011 htau hs1132011).elim
            · have hs1132013 : InSquare (103/320) (-77/320) (1/320) tau := by
                convert childUR hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1866.sound htau (by
                simp only [Batch0233.cell1866, Batch0233.tau1866, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132013 (by positivity) using 1 <;> norm_num)
        · have hs113203 : InSquare (51/160) (-37/160) (1/160) tau := by
            convert childUR hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx113203 | hx113203
          · rcases le_total tau.im (-37/160 : ℝ) with hy113203 | hy113203
            · have hs1132030 : InSquare (101/320) (-15/64) (1/320) tau := by
                convert childLL hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1867.sound htau (by
                simp only [Batch0233.cell1867, Batch0233.tau1867, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132030 (by positivity) using 1 <;> norm_num)
            · have hs1132032 : InSquare (101/320) (-73/320) (1/320) tau := by
                convert childUL hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1869.sound htau (by
                simp only [Batch0233.cell1869, Batch0233.tau1869, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy113203 | hy113203
            · have hs1132031 : InSquare (103/320) (-15/64) (1/320) tau := by
                convert childLR hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1868.sound htau (by
                simp only [Batch0233.cell1868, Batch0233.tau1868, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132031 (by positivity) using 1 <;> norm_num)
            · have hs1132033 : InSquare (103/320) (-73/320) (1/320) tau := by
                convert childUR hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1870.sound htau (by
                simp only [Batch0233.cell1870, Batch0233.tau1870, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132033 (by positivity) using 1 <;> norm_num)
    · have hs11322 : InSquare (5/16) (-17/80) (1/80) tau := by
        convert childUL hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11322 | hx11322
      · rcases le_total tau.im (-17/80 : ℝ) with hy11322 | hy11322
        · have hs113220 : InSquare (49/160) (-7/32) (1/160) tau := by
            convert childLL hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0690.sound htau (by
            simp only [Batch0086.cell0690, Batch0086.tau0690, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113220 (by positivity) using 1 <;> norm_num)
        · have hs113222 : InSquare (49/160) (-33/160) (1/160) tau := by
            convert childUL hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0692.sound htau (by
            simp only [Batch0086.cell0692, Batch0086.tau0692, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11322 | hy11322
        · have hs113221 : InSquare (51/160) (-7/32) (1/160) tau := by
            convert childLR hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0691.sound htau (by
            simp only [Batch0086.cell0691, Batch0086.tau0691, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113221 (by positivity) using 1 <;> norm_num)
        · have hs113223 : InSquare (51/160) (-33/160) (1/160) tau := by
            convert childUR hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0693.sound htau (by
            simp only [Batch0086.cell0693, Batch0086.tau0693, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1132 | hy1132
    · have hs11321 : InSquare (27/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx11321 | hx11321
      · rcases le_total tau.im (-19/80 : ℝ) with hy11321 | hy11321
        · have hs113210 : InSquare (53/160) (-39/160) (1/160) tau := by
            convert childLL hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113210 htau hs113210).elim
        · have hs113212 : InSquare (53/160) (-37/160) (1/160) tau := by
            convert childUL hs11321 hx11321 hy11321 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx113212 | hx113212
          · rcases le_total tau.im (-37/160 : ℝ) with hy113212 | hy113212
            · have hs1132120 : InSquare (21/64) (-15/64) (1/320) tau := by
                convert childLL hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact Batch0233.cell1871.sound htau (by
                simp only [Batch0233.cell1871, Batch0233.tau1871, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132120 (by positivity) using 1 <;> norm_num)
            · have hs1132122 : InSquare (21/64) (-73/320) (1/320) tau := by
                convert childUL hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact Batch0234.cell1872.sound htau (by
                simp only [Batch0234.cell1872, Batch0234.tau1872, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy113212 | hy113212
            · have hs1132121 : InSquare (107/320) (-15/64) (1/320) tau := by
                convert childLR hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact (outside_1132121 htau hs1132121).elim
            · have hs1132123 : InSquare (107/320) (-73/320) (1/320) tau := by
                convert childUR hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact (outside_1132123 htau hs1132123).elim
      · rcases le_total tau.im (-19/80 : ℝ) with hy11321 | hy11321
        · have hs113211 : InSquare (11/32) (-39/160) (1/160) tau := by
            convert childLR hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113211 htau hs113211).elim
        · have hs113213 : InSquare (11/32) (-37/160) (1/160) tau := by
            convert childUR hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113213 htau hs113213).elim
    · have hs11323 : InSquare (27/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx11323 | hx11323
      · rcases le_total tau.im (-17/80 : ℝ) with hy11323 | hy11323
        · have hs113230 : InSquare (53/160) (-7/32) (1/160) tau := by
            convert childLL hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx113230 | hx113230
          · rcases le_total tau.im (-7/32 : ℝ) with hy113230 | hy113230
            · have hs1132300 : InSquare (21/64) (-71/320) (1/320) tau := by
                convert childLL hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1873.sound htau (by
                simp only [Batch0234.cell1873, Batch0234.tau1873, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132300 (by positivity) using 1 <;> norm_num)
            · have hs1132302 : InSquare (21/64) (-69/320) (1/320) tau := by
                convert childUL hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1875.sound htau (by
                simp only [Batch0234.cell1875, Batch0234.tau1875, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy113230 | hy113230
            · have hs1132301 : InSquare (107/320) (-71/320) (1/320) tau := by
                convert childLR hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1874.sound htau (by
                simp only [Batch0234.cell1874, Batch0234.tau1874, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132301 (by positivity) using 1 <;> norm_num)
            · have hs1132303 : InSquare (107/320) (-69/320) (1/320) tau := by
                convert childUR hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1876.sound htau (by
                simp only [Batch0234.cell1876, Batch0234.tau1876, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132303 (by positivity) using 1 <;> norm_num)
        · have hs113232 : InSquare (53/160) (-33/160) (1/160) tau := by
            convert childUL hs11323 hx11323 hy11323 using 1 <;> norm_num
          exact Batch0086.cell0694.sound htau (by
            simp only [Batch0086.cell0694, Batch0086.tau0694, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11323 | hy11323
        · have hs113231 : InSquare (11/32) (-7/32) (1/160) tau := by
            convert childLR hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx113231 | hx113231
          · rcases le_total tau.im (-7/32 : ℝ) with hy113231 | hy113231
            · have hs1132310 : InSquare (109/320) (-71/320) (1/320) tau := by
                convert childLL hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132310 htau hs1132310).elim
            · have hs1132312 : InSquare (109/320) (-69/320) (1/320) tau := by
                convert childUL hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact Batch0234.cell1877.sound htau (by
                simp only [Batch0234.cell1877, Batch0234.tau1877, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy113231 | hy113231
            · have hs1132311 : InSquare (111/320) (-71/320) (1/320) tau := by
                convert childLR hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132311 htau hs1132311).elim
            · have hs1132313 : InSquare (111/320) (-69/320) (1/320) tau := by
                convert childUR hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132313 htau hs1132313).elim
        · have hs113233 : InSquare (11/32) (-33/160) (1/160) tau := by
            convert childUR hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx113233 | hx113233
          · rcases le_total tau.im (-33/160 : ℝ) with hy113233 | hy113233
            · have hs1132330 : InSquare (109/320) (-67/320) (1/320) tau := by
                convert childLL hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0234.cell1878.sound htau (by
                simp only [Batch0234.cell1878, Batch0234.tau1878, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132330 (by positivity) using 1 <;> norm_num)
            · have hs1132332 : InSquare (109/320) (-13/64) (1/320) tau := by
                convert childUL hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0234.cell1879.sound htau (by
                simp only [Batch0234.cell1879, Batch0234.tau1879, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-33/160 : ℝ) with hy113233 | hy113233
            · have hs1132331 : InSquare (111/320) (-67/320) (1/320) tau := by
                convert childLR hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact (outside_1132331 htau hs1132331).elim
            · have hs1132333 : InSquare (111/320) (-13/64) (1/320) tau := by
                convert childUR hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0235.cell1880.sound htau (by
                simp only [Batch0235.cell1880, Batch0235.tau1880, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1201 | hx1201
  · rcases le_total tau.im (-7/40 : ℝ) with hy1201 | hy1201
    · have hs12010 : InSquare (1/16) (-3/16) (1/80) tau := by
        convert childLL hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0145.sound htau (by
        simp only [Batch0018.cell0145, Batch0018.tau0145, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12010 (by positivity) using 1 <;> norm_num)
    · have hs12012 : InSquare (1/16) (-13/80) (1/80) tau := by
        convert childUL hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0147.sound htau (by
        simp only [Batch0018.cell0147, Batch0018.tau0147, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1201 | hy1201
    · have hs12011 : InSquare (7/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0146.sound htau (by
        simp only [Batch0018.cell0146, Batch0018.tau0146, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12011 (by positivity) using 1 <;> norm_num)
    · have hs12013 : InSquare (7/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0148.sound htau (by
        simp only [Batch0018.cell0148, Batch0018.tau0148, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1210 | hx1210
  · rcases le_total tau.im (-7/40 : ℝ) with hy1210 | hy1210
    · have hs12100 : InSquare (9/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0149.sound htau (by
        simp only [Batch0018.cell0149, Batch0018.tau0149, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12100 (by positivity) using 1 <;> norm_num)
    · have hs12102 : InSquare (9/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0151.sound htau (by
        simp only [Batch0018.cell0151, Batch0018.tau0151, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1210 | hy1210
    · have hs12101 : InSquare (11/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0150.sound htau (by
        simp only [Batch0018.cell0150, Batch0018.tau0150, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12101 (by positivity) using 1 <;> norm_num)
    · have hs12103 : InSquare (11/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0019.cell0152.sound htau (by
        simp only [Batch0019.cell0152, Batch0019.tau0152, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1211 | hx1211
  · rcases le_total tau.im (-7/40 : ℝ) with hy1211 | hy1211
    · have hs12110 : InSquare (13/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0153.sound htau (by
        simp only [Batch0019.cell0153, Batch0019.tau0153, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12110 (by positivity) using 1 <;> norm_num)
    · have hs12112 : InSquare (13/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0155.sound htau (by
        simp only [Batch0019.cell0155, Batch0019.tau0155, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1211 | hy1211
    · have hs12111 : InSquare (3/16) (-3/16) (1/80) tau := by
        convert childLR hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0154.sound htau (by
        simp only [Batch0019.cell0154, Batch0019.tau0154, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12111 (by positivity) using 1 <;> norm_num)
    · have hs12113 : InSquare (3/16) (-13/80) (1/80) tau := by
        convert childUR hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0156.sound htau (by
        simp only [Batch0019.cell0156, Batch0019.tau0156, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1213 | hx1213
  · rcases le_total tau.im (-1/8 : ℝ) with hy1213 | hy1213
    · have hs12130 : InSquare (13/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0157.sound htau (by
        simp only [Batch0019.cell0157, Batch0019.tau0157, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12130 (by positivity) using 1 <;> norm_num)
    · have hs12132 : InSquare (13/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0159.sound htau (by
        simp only [Batch0019.cell0159, Batch0019.tau0159, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1213 | hy1213
    · have hs12131 : InSquare (3/16) (-11/80) (1/80) tau := by
        convert childLR hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0158.sound htau (by
        simp only [Batch0019.cell0158, Batch0019.tau0158, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12131 (by positivity) using 1 <;> norm_num)
    · have hs12133 : InSquare (3/16) (-9/80) (1/80) tau := by
        convert childUR hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0020.cell0160.sound htau (by
        simp only [Batch0020.cell0160, Batch0020.tau0160, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1300 | hx1300
  · rcases le_total tau.im (-7/40 : ℝ) with hy1300 | hy1300
    · have hs13000 : InSquare (17/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0161.sound htau (by
        simp only [Batch0020.cell0161, Batch0020.tau0161, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13000 (by positivity) using 1 <;> norm_num)
    · have hs13002 : InSquare (17/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0162.sound htau (by
        simp only [Batch0020.cell0162, Batch0020.tau0162, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13002 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1300 | hy1300
    · have hs13001 : InSquare (19/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1300 hy1300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx13001 | hx13001
      · rcases le_total tau.im (-3/16 : ℝ) with hy13001 | hy13001
        · have hs130010 : InSquare (37/160) (-31/160) (1/160) tau := by
            convert childLL hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0086.cell0695.sound htau (by
            simp only [Batch0086.cell0695, Batch0086.tau0695, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130010 (by positivity) using 1 <;> norm_num)
        · have hs130012 : InSquare (37/160) (-29/160) (1/160) tau := by
            convert childUL hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0697.sound htau (by
            simp only [Batch0087.cell0697, Batch0087.tau0697, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13001 | hy13001
        · have hs130011 : InSquare (39/160) (-31/160) (1/160) tau := by
            convert childLR hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0696.sound htau (by
            simp only [Batch0087.cell0696, Batch0087.tau0696, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130011 (by positivity) using 1 <;> norm_num)
        · have hs130013 : InSquare (39/160) (-29/160) (1/160) tau := by
            convert childUR hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0698.sound htau (by
            simp only [Batch0087.cell0698, Batch0087.tau0698, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130013 (by positivity) using 1 <;> norm_num)
    · have hs13003 : InSquare (19/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0163.sound htau (by
        simp only [Batch0020.cell0163, Batch0020.tau0163, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1301 | hx1301
  · rcases le_total tau.im (-7/40 : ℝ) with hy1301 | hy1301
    · have hs13010 : InSquare (21/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx13010 | hx13010
      · rcases le_total tau.im (-3/16 : ℝ) with hy13010 | hy13010
        · have hs130100 : InSquare (41/160) (-31/160) (1/160) tau := by
            convert childLL hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0699.sound htau (by
            simp only [Batch0087.cell0699, Batch0087.tau0699, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130100 (by positivity) using 1 <;> norm_num)
        · have hs130102 : InSquare (41/160) (-29/160) (1/160) tau := by
            convert childUL hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0701.sound htau (by
            simp only [Batch0087.cell0701, Batch0087.tau0701, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13010 | hy13010
        · have hs130101 : InSquare (43/160) (-31/160) (1/160) tau := by
            convert childLR hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0700.sound htau (by
            simp only [Batch0087.cell0700, Batch0087.tau0700, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130101 (by positivity) using 1 <;> norm_num)
        · have hs130103 : InSquare (43/160) (-29/160) (1/160) tau := by
            convert childUR hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0702.sound htau (by
            simp only [Batch0087.cell0702, Batch0087.tau0702, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130103 (by positivity) using 1 <;> norm_num)
    · have hs13012 : InSquare (21/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1301 hy1301 using 1 <;> norm_num
      exact Batch0020.cell0164.sound htau (by
        simp only [Batch0020.cell0164, Batch0020.tau0164, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1301 | hy1301
    · have hs13011 : InSquare (23/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx13011 | hx13011
      · rcases le_total tau.im (-3/16 : ℝ) with hy13011 | hy13011
        · have hs130110 : InSquare (9/32) (-31/160) (1/160) tau := by
            convert childLL hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0087.cell0703.sound htau (by
            simp only [Batch0087.cell0703, Batch0087.tau0703, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130110 (by positivity) using 1 <;> norm_num)
        · have hs130112 : InSquare (9/32) (-29/160) (1/160) tau := by
            convert childUL hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0705.sound htau (by
            simp only [Batch0088.cell0705, Batch0088.tau0705, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13011 | hy13011
        · have hs130111 : InSquare (47/160) (-31/160) (1/160) tau := by
            convert childLR hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0704.sound htau (by
            simp only [Batch0088.cell0704, Batch0088.tau0704, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130111 (by positivity) using 1 <;> norm_num)
        · have hs130113 : InSquare (47/160) (-29/160) (1/160) tau := by
            convert childUR hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0706.sound htau (by
            simp only [Batch0088.cell0706, Batch0088.tau0706, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130113 (by positivity) using 1 <;> norm_num)
    · have hs13013 : InSquare (23/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx13013 | hx13013
      · rcases le_total tau.im (-13/80 : ℝ) with hy13013 | hy13013
        · have hs130130 : InSquare (9/32) (-27/160) (1/160) tau := by
            convert childLL hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0707.sound htau (by
            simp only [Batch0088.cell0707, Batch0088.tau0707, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130130 (by positivity) using 1 <;> norm_num)
        · have hs130132 : InSquare (9/32) (-5/32) (1/160) tau := by
            convert childUL hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0709.sound htau (by
            simp only [Batch0088.cell0709, Batch0088.tau0709, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13013 | hy13013
        · have hs130131 : InSquare (47/160) (-27/160) (1/160) tau := by
            convert childLR hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0708.sound htau (by
            simp only [Batch0088.cell0708, Batch0088.tau0708, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130131 (by positivity) using 1 <;> norm_num)
        · have hs130133 : InSquare (47/160) (-5/32) (1/160) tau := by
            convert childUR hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0710.sound htau (by
            simp only [Batch0088.cell0710, Batch0088.tau0710, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1302 | hx1302
  · rcases le_total tau.im (-1/8 : ℝ) with hy1302 | hy1302
    · have hs13020 : InSquare (17/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0165.sound htau (by
        simp only [Batch0020.cell0165, Batch0020.tau0165, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13020 (by positivity) using 1 <;> norm_num)
    · have hs13022 : InSquare (17/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0167.sound htau (by
        simp only [Batch0020.cell0167, Batch0020.tau0167, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1302 | hy1302
    · have hs13021 : InSquare (19/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0166.sound htau (by
        simp only [Batch0020.cell0166, Batch0020.tau0166, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13021 (by positivity) using 1 <;> norm_num)
    · have hs13023 : InSquare (19/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0021.cell0168.sound htau (by
        simp only [Batch0021.cell0168, Batch0021.tau0168, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1303 | hx1303
  · rcases le_total tau.im (-1/8 : ℝ) with hy1303 | hy1303
    · have hs13030 : InSquare (21/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0169.sound htau (by
        simp only [Batch0021.cell0169, Batch0021.tau0169, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13030 (by positivity) using 1 <;> norm_num)
    · have hs13032 : InSquare (21/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0171.sound htau (by
        simp only [Batch0021.cell0171, Batch0021.tau0171, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1303 | hy1303
    · have hs13031 : InSquare (23/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0170.sound htau (by
        simp only [Batch0021.cell0170, Batch0021.tau0170, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13031 (by positivity) using 1 <;> norm_num)
    · have hs13033 : InSquare (23/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0172.sound htau (by
        simp only [Batch0021.cell0172, Batch0021.tau0172, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1310 | hx1310
  · rcases le_total tau.im (-7/40 : ℝ) with hy1310 | hy1310
    · have hs13100 : InSquare (5/16) (-3/16) (1/80) tau := by
        convert childLL hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13100 | hx13100
      · rcases le_total tau.im (-3/16 : ℝ) with hy13100 | hy13100
        · have hs131000 : InSquare (49/160) (-31/160) (1/160) tau := by
            convert childLL hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0088.cell0711.sound htau (by
            simp only [Batch0088.cell0711, Batch0088.tau0711, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131000 (by positivity) using 1 <;> norm_num)
        · have hs131002 : InSquare (49/160) (-29/160) (1/160) tau := by
            convert childUL hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0713.sound htau (by
            simp only [Batch0089.cell0713, Batch0089.tau0713, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13100 | hy13100
        · have hs131001 : InSquare (51/160) (-31/160) (1/160) tau := by
            convert childLR hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0712.sound htau (by
            simp only [Batch0089.cell0712, Batch0089.tau0712, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131001 (by positivity) using 1 <;> norm_num)
        · have hs131003 : InSquare (51/160) (-29/160) (1/160) tau := by
            convert childUR hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0714.sound htau (by
            simp only [Batch0089.cell0714, Batch0089.tau0714, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131003 (by positivity) using 1 <;> norm_num)
    · have hs13102 : InSquare (5/16) (-13/80) (1/80) tau := by
        convert childUL hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13102 | hx13102
      · rcases le_total tau.im (-13/80 : ℝ) with hy13102 | hy13102
        · have hs131020 : InSquare (49/160) (-27/160) (1/160) tau := by
            convert childLL hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0089.cell0719.sound htau (by
            simp only [Batch0089.cell0719, Batch0089.tau0719, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131020 (by positivity) using 1 <;> norm_num)
        · have hs131022 : InSquare (49/160) (-5/32) (1/160) tau := by
            convert childUL hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0721.sound htau (by
            simp only [Batch0090.cell0721, Batch0090.tau0721, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13102 | hy13102
        · have hs131021 : InSquare (51/160) (-27/160) (1/160) tau := by
            convert childLR hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0720.sound htau (by
            simp only [Batch0090.cell0720, Batch0090.tau0720, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131021 (by positivity) using 1 <;> norm_num)
        · have hs131023 : InSquare (51/160) (-5/32) (1/160) tau := by
            convert childUR hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0722.sound htau (by
            simp only [Batch0090.cell0722, Batch0090.tau0722, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1310 | hy1310
    · have hs13101 : InSquare (27/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13101 | hx13101
      · rcases le_total tau.im (-3/16 : ℝ) with hy13101 | hy13101
        · have hs131010 : InSquare (53/160) (-31/160) (1/160) tau := by
            convert childLL hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0715.sound htau (by
            simp only [Batch0089.cell0715, Batch0089.tau0715, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131010 (by positivity) using 1 <;> norm_num)
        · have hs131012 : InSquare (53/160) (-29/160) (1/160) tau := by
            convert childUL hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0717.sound htau (by
            simp only [Batch0089.cell0717, Batch0089.tau0717, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13101 | hy13101
        · have hs131011 : InSquare (11/32) (-31/160) (1/160) tau := by
            convert childLR hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0716.sound htau (by
            simp only [Batch0089.cell0716, Batch0089.tau0716, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131011 (by positivity) using 1 <;> norm_num)
        · have hs131013 : InSquare (11/32) (-29/160) (1/160) tau := by
            convert childUR hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0718.sound htau (by
            simp only [Batch0089.cell0718, Batch0089.tau0718, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131013 (by positivity) using 1 <;> norm_num)
    · have hs13103 : InSquare (27/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13103 | hx13103
      · rcases le_total tau.im (-13/80 : ℝ) with hy13103 | hy13103
        · have hs131030 : InSquare (53/160) (-27/160) (1/160) tau := by
            convert childLL hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0723.sound htau (by
            simp only [Batch0090.cell0723, Batch0090.tau0723, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131030 (by positivity) using 1 <;> norm_num)
        · have hs131032 : InSquare (53/160) (-5/32) (1/160) tau := by
            convert childUL hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0725.sound htau (by
            simp only [Batch0090.cell0725, Batch0090.tau0725, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13103 | hy13103
        · have hs131031 : InSquare (11/32) (-27/160) (1/160) tau := by
            convert childLR hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0724.sound htau (by
            simp only [Batch0090.cell0724, Batch0090.tau0724, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131031 (by positivity) using 1 <;> norm_num)
        · have hs131033 : InSquare (11/32) (-5/32) (1/160) tau := by
            convert childUR hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0726.sound htau (by
            simp only [Batch0090.cell0726, Batch0090.tau0726, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_13111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (-3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_13113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (-13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (-31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (-29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (113/320) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311003 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (-61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1311 | hx1311
  · rcases le_total tau.im (-7/40 : ℝ) with hy1311 | hy1311
    · have hs13110 : InSquare (29/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1311 hy1311 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13110 | hx13110
      · rcases le_total tau.im (-3/16 : ℝ) with hy13110 | hy13110
        · have hs131100 : InSquare (57/160) (-31/160) (1/160) tau := by
            convert childLL hs13110 hx13110 hy13110 using 1 <;> norm_num
          rcases le_total tau.re (57/160 : ℝ) with hx131100 | hx131100
          · rcases le_total tau.im (-31/160 : ℝ) with hy131100 | hy131100
            · have hs1311000 : InSquare (113/320) (-63/320) (1/320) tau := by
                convert childLL hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311000 htau hs1311000).elim
            · have hs1311002 : InSquare (113/320) (-61/320) (1/320) tau := by
                convert childUL hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact Batch0235.cell1881.sound htau (by
                simp only [Batch0235.cell1881, Batch0235.tau1881, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1311002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-31/160 : ℝ) with hy131100 | hy131100
            · have hs1311001 : InSquare (23/64) (-63/320) (1/320) tau := by
                convert childLR hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311001 htau hs1311001).elim
            · have hs1311003 : InSquare (23/64) (-61/320) (1/320) tau := by
                convert childUR hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311003 htau hs1311003).elim
        · have hs131102 : InSquare (57/160) (-29/160) (1/160) tau := by
            convert childUL hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact Batch0090.cell0727.sound htau (by
            simp only [Batch0090.cell0727, Batch0090.tau0727, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13110 | hy13110
        · have hs131101 : InSquare (59/160) (-31/160) (1/160) tau := by
            convert childLR hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact (outside_131101 htau hs131101).elim
        · have hs131103 : InSquare (59/160) (-29/160) (1/160) tau := by
            convert childUR hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact (outside_131103 htau hs131103).elim
    · have hs13112 : InSquare (29/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1311 hy1311 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13112 | hx13112
      · rcases le_total tau.im (-13/80 : ℝ) with hy13112 | hy13112
        · have hs131120 : InSquare (57/160) (-27/160) (1/160) tau := by
            convert childLL hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0728.sound htau (by
            simp only [Batch0091.cell0728, Batch0091.tau0728, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131120 (by positivity) using 1 <;> norm_num)
        · have hs131122 : InSquare (57/160) (-5/32) (1/160) tau := by
            convert childUL hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0730.sound htau (by
            simp only [Batch0091.cell0730, Batch0091.tau0730, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13112 | hy13112
        · have hs131121 : InSquare (59/160) (-27/160) (1/160) tau := by
            convert childLR hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0729.sound htau (by
            simp only [Batch0091.cell0729, Batch0091.tau0729, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131121 (by positivity) using 1 <;> norm_num)
        · have hs131123 : InSquare (59/160) (-5/32) (1/160) tau := by
            convert childUR hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0731.sound htau (by
            simp only [Batch0091.cell0731, Batch0091.tau0731, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1311 | hy1311
    · have hs13111 : InSquare (31/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1311 hy1311 using 1 <;> norm_num
      exact (outside_13111 htau hs13111).elim
    · have hs13113 : InSquare (31/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1311 hy1311 using 1 <;> norm_num
      exact (outside_13113 htau hs13113).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1312 | hx1312
  · rcases le_total tau.im (-1/8 : ℝ) with hy1312 | hy1312
    · have hs13120 : InSquare (5/16) (-11/80) (1/80) tau := by
        convert childLL hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13120 | hx13120
      · rcases le_total tau.im (-11/80 : ℝ) with hy13120 | hy13120
        · have hs131200 : InSquare (49/160) (-23/160) (1/160) tau := by
            convert childLL hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0732.sound htau (by
            simp only [Batch0091.cell0732, Batch0091.tau0732, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131200 (by positivity) using 1 <;> norm_num)
        · have hs131202 : InSquare (49/160) (-21/160) (1/160) tau := by
            convert childUL hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0734.sound htau (by
            simp only [Batch0091.cell0734, Batch0091.tau0734, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13120 | hy13120
        · have hs131201 : InSquare (51/160) (-23/160) (1/160) tau := by
            convert childLR hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0733.sound htau (by
            simp only [Batch0091.cell0733, Batch0091.tau0733, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131201 (by positivity) using 1 <;> norm_num)
        · have hs131203 : InSquare (51/160) (-21/160) (1/160) tau := by
            convert childUR hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0735.sound htau (by
            simp only [Batch0091.cell0735, Batch0091.tau0735, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131203 (by positivity) using 1 <;> norm_num)
    · have hs13122 : InSquare (5/16) (-9/80) (1/80) tau := by
        convert childUL hs hx1312 hy1312 using 1 <;> norm_num
      exact Batch0021.cell0173.sound htau (by
        simp only [Batch0021.cell0173, Batch0021.tau0173, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1312 | hy1312
    · have hs13121 : InSquare (27/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13121 | hx13121
      · rcases le_total tau.im (-11/80 : ℝ) with hy13121 | hy13121
        · have hs131210 : InSquare (53/160) (-23/160) (1/160) tau := by
            convert childLL hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0736.sound htau (by
            simp only [Batch0092.cell0736, Batch0092.tau0736, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131210 (by positivity) using 1 <;> norm_num)
        · have hs131212 : InSquare (53/160) (-21/160) (1/160) tau := by
            convert childUL hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0738.sound htau (by
            simp only [Batch0092.cell0738, Batch0092.tau0738, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13121 | hy13121
        · have hs131211 : InSquare (11/32) (-23/160) (1/160) tau := by
            convert childLR hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0737.sound htau (by
            simp only [Batch0092.cell0737, Batch0092.tau0737, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131211 (by positivity) using 1 <;> norm_num)
        · have hs131213 : InSquare (11/32) (-21/160) (1/160) tau := by
            convert childUR hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0739.sound htau (by
            simp only [Batch0092.cell0739, Batch0092.tau0739, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131213 (by positivity) using 1 <;> norm_num)
    · have hs13123 : InSquare (27/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13123 | hx13123
      · rcases le_total tau.im (-9/80 : ℝ) with hy13123 | hy13123
        · have hs131230 : InSquare (53/160) (-19/160) (1/160) tau := by
            convert childLL hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0740.sound htau (by
            simp only [Batch0092.cell0740, Batch0092.tau0740, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131230 (by positivity) using 1 <;> norm_num)
        · have hs131232 : InSquare (53/160) (-17/160) (1/160) tau := by
            convert childUL hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0742.sound htau (by
            simp only [Batch0092.cell0742, Batch0092.tau0742, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13123 | hy13123
        · have hs131231 : InSquare (11/32) (-19/160) (1/160) tau := by
            convert childLR hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0741.sound htau (by
            simp only [Batch0092.cell0741, Batch0092.tau0741, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131231 (by positivity) using 1 <;> norm_num)
        · have hs131233 : InSquare (11/32) (-17/160) (1/160) tau := by
            convert childUR hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0743.sound htau (by
            simp only [Batch0092.cell0743, Batch0092.tau0743, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_131311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1313 | hx1313
  · rcases le_total tau.im (-1/8 : ℝ) with hy1313 | hy1313
    · have hs13130 : InSquare (29/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13130 | hx13130
      · rcases le_total tau.im (-11/80 : ℝ) with hy13130 | hy13130
        · have hs131300 : InSquare (57/160) (-23/160) (1/160) tau := by
            convert childLL hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0744.sound htau (by
            simp only [Batch0093.cell0744, Batch0093.tau0744, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131300 (by positivity) using 1 <;> norm_num)
        · have hs131302 : InSquare (57/160) (-21/160) (1/160) tau := by
            convert childUL hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0746.sound htau (by
            simp only [Batch0093.cell0746, Batch0093.tau0746, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13130 | hy13130
        · have hs131301 : InSquare (59/160) (-23/160) (1/160) tau := by
            convert childLR hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0745.sound htau (by
            simp only [Batch0093.cell0745, Batch0093.tau0745, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131301 (by positivity) using 1 <;> norm_num)
        · have hs131303 : InSquare (59/160) (-21/160) (1/160) tau := by
            convert childUR hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0747.sound htau (by
            simp only [Batch0093.cell0747, Batch0093.tau0747, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131303 (by positivity) using 1 <;> norm_num)
    · have hs13132 : InSquare (29/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13132 | hx13132
      · rcases le_total tau.im (-9/80 : ℝ) with hy13132 | hy13132
        · have hs131320 : InSquare (57/160) (-19/160) (1/160) tau := by
            convert childLL hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0093.cell0750.sound htau (by
            simp only [Batch0093.cell0750, Batch0093.tau0750, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131320 (by positivity) using 1 <;> norm_num)
        · have hs131322 : InSquare (57/160) (-17/160) (1/160) tau := by
            convert childUL hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0094.cell0752.sound htau (by
            simp only [Batch0094.cell0752, Batch0094.tau0752, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13132 | hy13132
        · have hs131321 : InSquare (59/160) (-19/160) (1/160) tau := by
            convert childLR hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0093.cell0751.sound htau (by
            simp only [Batch0093.cell0751, Batch0093.tau0751, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131321 (by positivity) using 1 <;> norm_num)
        · have hs131323 : InSquare (59/160) (-17/160) (1/160) tau := by
            convert childUR hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0094.cell0753.sound htau (by
            simp only [Batch0094.cell0753, Batch0094.tau0753, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1313 | hy1313
    · have hs13131 : InSquare (31/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13131 | hx13131
      · rcases le_total tau.im (-11/80 : ℝ) with hy13131 | hy13131
        · have hs131310 : InSquare (61/160) (-23/160) (1/160) tau := by
            convert childLL hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact Batch0093.cell0748.sound htau (by
            simp only [Batch0093.cell0748, Batch0093.tau0748, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131310 (by positivity) using 1 <;> norm_num)
        · have hs131312 : InSquare (61/160) (-21/160) (1/160) tau := by
            convert childUL hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact Batch0093.cell0749.sound htau (by
            simp only [Batch0093.cell0749, Batch0093.tau0749, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13131 | hy13131
        · have hs131311 : InSquare (63/160) (-23/160) (1/160) tau := by
            convert childLR hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact (outside_131311 htau hs131311).elim
        · have hs131313 : InSquare (63/160) (-21/160) (1/160) tau := by
            convert childUR hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact (outside_131313 htau hs131313).elim
    · have hs13133 : InSquare (31/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13133 | hx13133
      · rcases le_total tau.im (-9/80 : ℝ) with hy13133 | hy13133
        · have hs131330 : InSquare (61/160) (-19/160) (1/160) tau := by
            convert childLL hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact Batch0094.cell0754.sound htau (by
            simp only [Batch0094.cell0754, Batch0094.tau0754, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131330 (by positivity) using 1 <;> norm_num)
        · have hs131332 : InSquare (61/160) (-17/160) (1/160) tau := by
            convert childUL hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact Batch0094.cell0755.sound htau (by
            simp only [Batch0094.cell0755, Batch0094.tau0755, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13133 | hy13133
        · have hs131331 : InSquare (63/160) (-19/160) (1/160) tau := by
            convert childLR hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact (outside_131331 htau hs131331).elim
        · have hs131333 : InSquare (63/160) (-17/160) (1/160) tau := by
            convert childUR hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact (outside_131333 htau hs131333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1320 | hx1320
  · rcases le_total tau.im (-3/40 : ℝ) with hy1320 | hy1320
    · have hs13200 : InSquare (17/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0021.cell0174.sound htau (by
        simp only [Batch0021.cell0174, Batch0021.tau0174, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13200 (by positivity) using 1 <;> norm_num)
    · have hs13202 : InSquare (17/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0022.cell0176.sound htau (by
        simp only [Batch0022.cell0176, Batch0022.tau0176, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1320 | hy1320
    · have hs13201 : InSquare (19/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0021.cell0175.sound htau (by
        simp only [Batch0021.cell0175, Batch0021.tau0175, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13201 (by positivity) using 1 <;> norm_num)
    · have hs13203 : InSquare (19/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0022.cell0177.sound htau (by
        simp only [Batch0022.cell0177, Batch0022.tau0177, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1321 | hx1321
  · rcases le_total tau.im (-3/40 : ℝ) with hy1321 | hy1321
    · have hs13210 : InSquare (21/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0178.sound htau (by
        simp only [Batch0022.cell0178, Batch0022.tau0178, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13210 (by positivity) using 1 <;> norm_num)
    · have hs13212 : InSquare (21/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0180.sound htau (by
        simp only [Batch0022.cell0180, Batch0022.tau0180, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1321 | hy1321
    · have hs13211 : InSquare (23/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0179.sound htau (by
        simp only [Batch0022.cell0179, Batch0022.tau0179, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13211 (by positivity) using 1 <;> norm_num)
    · have hs13213 : InSquare (23/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0181.sound htau (by
        simp only [Batch0022.cell0181, Batch0022.tau0181, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1323 | hx1323
  · rcases le_total tau.im (-1/40 : ℝ) with hy1323 | hy1323
    · have hs13230 : InSquare (21/80) (-3/80) (1/80) tau := by
        convert childLL hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0022.cell0182.sound htau (by
        simp only [Batch0022.cell0182, Batch0022.tau0182, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13230 (by positivity) using 1 <;> norm_num)
    · have hs13232 : InSquare (21/80) (-1/80) (1/80) tau := by
        convert childUL hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0023.cell0184.sound htau (by
        simp only [Batch0023.cell0184, Batch0023.tau0184, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1323 | hy1323
    · have hs13231 : InSquare (23/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0022.cell0183.sound htau (by
        simp only [Batch0022.cell0183, Batch0022.tau0183, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13231 (by positivity) using 1 <;> norm_num)
    · have hs13233 : InSquare (23/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0023.cell0185.sound htau (by
        simp only [Batch0023.cell0185, Batch0023.tau0185, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323

end


