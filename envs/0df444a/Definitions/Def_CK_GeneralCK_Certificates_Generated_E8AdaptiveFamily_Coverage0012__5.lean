-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0012__5
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage0012__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:26:03.925812+00:00
-- url     : https://prove2.me/theorems/e4261fbf-b577-4904-9118-3560409b1fe5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012 (+4 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0012 (+4 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0013, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0021, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0023, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage0030).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0151
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0152
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0153
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0154
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0155
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0320
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0321
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0322
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0163
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_00120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (-5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/64) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (-97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0012 | hx0012
  · rcases le_total tau.im (-13/40 : ℝ) with hy0012 | hy0012
    · have hs00120 : InSquare (-23/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00120 htau hs00120).elim
    · have hs00122 : InSquare (-23/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00122 htau hs00122).elim
  · rcases le_total tau.im (-13/40 : ℝ) with hy0012 | hy0012
    · have hs00121 : InSquare (-21/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00121 htau hs00121).elim
    · have hs00123 : InSquare (-21/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0012 hy0012 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00123 | hx00123
      · rcases le_total tau.im (-5/16 : ℝ) with hy00123 | hy00123
        · have hs001230 : InSquare (-43/160) (-51/160) (1/160) tau := by
            convert childLL hs00123 hx00123 hy00123 using 1 <;> norm_num
          exact (outside_001230 htau hs001230).elim
        · have hs001232 : InSquare (-43/160) (-49/160) (1/160) tau := by
            convert childUL hs00123 hx00123 hy00123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx001232 | hx001232
          · rcases le_total tau.im (-49/160 : ℝ) with hy001232 | hy001232
            · have hs0012320 : InSquare (-87/320) (-99/320) (1/320) tau := by
                convert childLL hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012320 htau hs0012320).elim
            · have hs0012322 : InSquare (-87/320) (-97/320) (1/320) tau := by
                convert childUL hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012322 htau hs0012322).elim
          · rcases le_total tau.im (-49/160 : ℝ) with hy001232 | hy001232
            · have hs0012321 : InSquare (-17/64) (-99/320) (1/320) tau := by
                convert childLR hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012321 htau hs0012321).elim
            · have hs0012323 : InSquare (-17/64) (-97/320) (1/320) tau := by
                convert childUR hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact Batch0150.cell1200.sound htau (by
                simp only [Batch0150.cell1200, Batch0150.tau1200, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00123 | hy00123
        · have hs001231 : InSquare (-41/160) (-51/160) (1/160) tau := by
            convert childLR hs00123 hx00123 hy00123 using 1 <;> norm_num
          exact (outside_001231 htau hs001231).elim
        · have hs001233 : InSquare (-41/160) (-49/160) (1/160) tau := by
            convert childUR hs00123 hx00123 hy00123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx001233 | hx001233
          · rcases le_total tau.im (-49/160 : ℝ) with hy001233 | hy001233
            · have hs0012330 : InSquare (-83/320) (-99/320) (1/320) tau := by
                convert childLL hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1201.sound htau (by
                simp only [Batch0150.cell1201, Batch0150.tau1201, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012330 (by positivity) using 1 <;> norm_num)
            · have hs0012332 : InSquare (-83/320) (-97/320) (1/320) tau := by
                convert childUL hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1203.sound htau (by
                simp only [Batch0150.cell1203, Batch0150.tau1203, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001233 | hy001233
            · have hs0012331 : InSquare (-81/320) (-99/320) (1/320) tau := by
                convert childLR hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1202.sound htau (by
                simp only [Batch0150.cell1202, Batch0150.tau1202, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012331 (by positivity) using 1 <;> norm_num)
            · have hs0012333 : InSquare (-81/320) (-97/320) (1/320) tau := by
                convert childUR hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1204.sound htau (by
                simp only [Batch0150.cell1204, Batch0150.tau1204, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_001300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (-53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/64) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/320) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-69/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (-109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-67/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/320) (-103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-149/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (-209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-137/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (-217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-131/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-129/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-143/640) (-43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0013 | hx0013
  · rcases le_total tau.im (-13/40 : ℝ) with hy0013 | hy0013
    · have hs00130 : InSquare (-19/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00130 | hx00130
      · rcases le_total tau.im (-27/80 : ℝ) with hy00130 | hy00130
        · have hs001300 : InSquare (-39/160) (-11/32) (1/160) tau := by
            convert childLL hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001300 htau hs001300).elim
        · have hs001302 : InSquare (-39/160) (-53/160) (1/160) tau := by
            convert childUL hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001302 htau hs001302).elim
      · rcases le_total tau.im (-27/80 : ℝ) with hy00130 | hy00130
        · have hs001301 : InSquare (-37/160) (-11/32) (1/160) tau := by
            convert childLR hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001301 htau hs001301).elim
        · have hs001303 : InSquare (-37/160) (-53/160) (1/160) tau := by
            convert childUR hs00130 hx00130 hy00130 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001303 | hx001303
          · rcases le_total tau.im (-53/160 : ℝ) with hy001303 | hy001303
            · have hs0013030 : InSquare (-15/64) (-107/320) (1/320) tau := by
                convert childLL hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact (outside_0013030 htau hs0013030).elim
            · have hs0013032 : InSquare (-15/64) (-21/64) (1/320) tau := by
                convert childUL hs001303 hx001303 hy001303 using 1 <;> norm_num
              rcases le_total tau.re (-15/64 : ℝ) with hx0013032 | hx0013032
              · rcases le_total tau.im (-21/64 : ℝ) with hy0013032 | hy0013032
                · have hs00130320 : InSquare (-151/640) (-211/640) (1/640) tau := by
                    convert childLL hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130320 htau hs00130320).elim
                · have hs00130322 : InSquare (-151/640) (-209/640) (1/640) tau := by
                    convert childUL hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130322 htau hs00130322).elim
              · rcases le_total tau.im (-21/64 : ℝ) with hy0013032 | hy0013032
                · have hs00130321 : InSquare (-149/640) (-211/640) (1/640) tau := by
                    convert childLR hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130321 htau hs00130321).elim
                · have hs00130323 : InSquare (-149/640) (-209/640) (1/640) tau := by
                    convert childUR hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact Batch0320.cell2564.sound htau (by
                    simp only [Batch0320.cell2564, Batch0320.tau2564, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00130323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001303 | hy001303
            · have hs0013031 : InSquare (-73/320) (-107/320) (1/320) tau := by
                convert childLR hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact (outside_0013031 htau hs0013031).elim
            · have hs0013033 : InSquare (-73/320) (-21/64) (1/320) tau := by
                convert childUR hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact Batch0150.cell1205.sound htau (by
                simp only [Batch0150.cell1205, Batch0150.tau1205, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013033 (by positivity) using 1 <;> norm_num)
    · have hs00132 : InSquare (-19/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00132 | hx00132
      · rcases le_total tau.im (-5/16 : ℝ) with hy00132 | hy00132
        · have hs001320 : InSquare (-39/160) (-51/160) (1/160) tau := by
            convert childLL hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx001320 | hx001320
          · rcases le_total tau.im (-51/160 : ℝ) with hy001320 | hy001320
            · have hs0013200 : InSquare (-79/320) (-103/320) (1/320) tau := by
                convert childLL hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact (outside_0013200 htau hs0013200).elim
            · have hs0013202 : InSquare (-79/320) (-101/320) (1/320) tau := by
                convert childUL hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1214.sound htau (by
                simp only [Batch0151.cell1214, Batch0151.tau1214, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001320 | hy001320
            · have hs0013201 : InSquare (-77/320) (-103/320) (1/320) tau := by
                convert childLR hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1213.sound htau (by
                simp only [Batch0151.cell1213, Batch0151.tau1213, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013201 (by positivity) using 1 <;> norm_num)
            · have hs0013203 : InSquare (-77/320) (-101/320) (1/320) tau := by
                convert childUR hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1215.sound htau (by
                simp only [Batch0151.cell1215, Batch0151.tau1215, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013203 (by positivity) using 1 <;> norm_num)
        · have hs001322 : InSquare (-39/160) (-49/160) (1/160) tau := by
            convert childUL hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx001322 | hx001322
          · rcases le_total tau.im (-49/160 : ℝ) with hy001322 | hy001322
            · have hs0013220 : InSquare (-79/320) (-99/320) (1/320) tau := by
                convert childLL hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1220.sound htau (by
                simp only [Batch0152.cell1220, Batch0152.tau1220, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013220 (by positivity) using 1 <;> norm_num)
            · have hs0013222 : InSquare (-79/320) (-97/320) (1/320) tau := by
                convert childUL hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1222.sound htau (by
                simp only [Batch0152.cell1222, Batch0152.tau1222, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001322 | hy001322
            · have hs0013221 : InSquare (-77/320) (-99/320) (1/320) tau := by
                convert childLR hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1221.sound htau (by
                simp only [Batch0152.cell1221, Batch0152.tau1221, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013221 (by positivity) using 1 <;> norm_num)
            · have hs0013223 : InSquare (-77/320) (-97/320) (1/320) tau := by
                convert childUR hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1223.sound htau (by
                simp only [Batch0152.cell1223, Batch0152.tau1223, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00132 | hy00132
        · have hs001321 : InSquare (-37/160) (-51/160) (1/160) tau := by
            convert childLR hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001321 | hx001321
          · rcases le_total tau.im (-51/160 : ℝ) with hy001321 | hy001321
            · have hs0013210 : InSquare (-15/64) (-103/320) (1/320) tau := by
                convert childLL hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1216.sound htau (by
                simp only [Batch0152.cell1216, Batch0152.tau1216, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013210 (by positivity) using 1 <;> norm_num)
            · have hs0013212 : InSquare (-15/64) (-101/320) (1/320) tau := by
                convert childUL hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1218.sound htau (by
                simp only [Batch0152.cell1218, Batch0152.tau1218, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001321 | hy001321
            · have hs0013211 : InSquare (-73/320) (-103/320) (1/320) tau := by
                convert childLR hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1217.sound htau (by
                simp only [Batch0152.cell1217, Batch0152.tau1217, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013211 (by positivity) using 1 <;> norm_num)
            · have hs0013213 : InSquare (-73/320) (-101/320) (1/320) tau := by
                convert childUR hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1219.sound htau (by
                simp only [Batch0152.cell1219, Batch0152.tau1219, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013213 (by positivity) using 1 <;> norm_num)
        · have hs001323 : InSquare (-37/160) (-49/160) (1/160) tau := by
            convert childUR hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001323 | hx001323
          · rcases le_total tau.im (-49/160 : ℝ) with hy001323 | hy001323
            · have hs0013230 : InSquare (-15/64) (-99/320) (1/320) tau := by
                convert childLL hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1224.sound htau (by
                simp only [Batch0153.cell1224, Batch0153.tau1224, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013230 (by positivity) using 1 <;> norm_num)
            · have hs0013232 : InSquare (-15/64) (-97/320) (1/320) tau := by
                convert childUL hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1226.sound htau (by
                simp only [Batch0153.cell1226, Batch0153.tau1226, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001323 | hy001323
            · have hs0013231 : InSquare (-73/320) (-99/320) (1/320) tau := by
                convert childLR hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1225.sound htau (by
                simp only [Batch0153.cell1225, Batch0153.tau1225, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013231 (by positivity) using 1 <;> norm_num)
            · have hs0013233 : InSquare (-73/320) (-97/320) (1/320) tau := by
                convert childUR hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1227.sound htau (by
                simp only [Batch0153.cell1227, Batch0153.tau1227, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0013 | hy0013
    · have hs00131 : InSquare (-17/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00131 | hx00131
      · rcases le_total tau.im (-27/80 : ℝ) with hy00131 | hy00131
        · have hs001310 : InSquare (-7/32) (-11/32) (1/160) tau := by
            convert childLL hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001310 | hx001310
          · rcases le_total tau.im (-11/32 : ℝ) with hy001310 | hy001310
            · have hs0013100 : InSquare (-71/320) (-111/320) (1/320) tau := by
                convert childLL hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013100 htau hs0013100).elim
            · have hs0013102 : InSquare (-71/320) (-109/320) (1/320) tau := by
                convert childUL hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013102 htau hs0013102).elim
          · rcases le_total tau.im (-11/32 : ℝ) with hy001310 | hy001310
            · have hs0013101 : InSquare (-69/320) (-111/320) (1/320) tau := by
                convert childLR hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013101 htau hs0013101).elim
            · have hs0013103 : InSquare (-69/320) (-109/320) (1/320) tau := by
                convert childUR hs001310 hx001310 hy001310 using 1 <;> norm_num
              rcases le_total tau.re (-69/320 : ℝ) with hx0013103 | hx0013103
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013103 | hy0013103
                · have hs00131030 : InSquare (-139/640) (-219/640) (1/640) tau := by
                    convert childLL hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131030 htau hs00131030).elim
                · have hs00131032 : InSquare (-139/640) (-217/640) (1/640) tau := by
                    convert childUL hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131032 htau hs00131032).elim
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013103 | hy0013103
                · have hs00131031 : InSquare (-137/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131031 htau hs00131031).elim
                · have hs00131033 : InSquare (-137/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact Batch0320.cell2565.sound htau (by
                    simp only [Batch0320.cell2565, Batch0320.tau2565, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131033 (by positivity) using 1 <;> norm_num)
        · have hs001312 : InSquare (-7/32) (-53/160) (1/160) tau := by
            convert childUL hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001312 | hx001312
          · rcases le_total tau.im (-53/160 : ℝ) with hy001312 | hy001312
            · have hs0013120 : InSquare (-71/320) (-107/320) (1/320) tau := by
                convert childLL hs001312 hx001312 hy001312 using 1 <;> norm_num
              rcases le_total tau.re (-71/320 : ℝ) with hx0013120 | hx0013120
              · rcases le_total tau.im (-107/320 : ℝ) with hy0013120 | hy0013120
                · have hs00131200 : InSquare (-143/640) (-43/128) (1/640) tau := by
                    convert childLL hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact (outside_00131200 htau hs00131200).elim
                · have hs00131202 : InSquare (-143/640) (-213/640) (1/640) tau := by
                    convert childUL hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2577.sound htau (by
                    simp only [Batch0322.cell2577, Batch0322.tau2577, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-107/320 : ℝ) with hy0013120 | hy0013120
                · have hs00131201 : InSquare (-141/640) (-43/128) (1/640) tau := by
                    convert childLR hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2576.sound htau (by
                    simp only [Batch0322.cell2576, Batch0322.tau2576, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131201 (by positivity) using 1 <;> norm_num)
                · have hs00131203 : InSquare (-141/640) (-213/640) (1/640) tau := by
                    convert childUR hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2578.sound htau (by
                    simp only [Batch0322.cell2578, Batch0322.tau2578, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131203 (by positivity) using 1 <;> norm_num)
            · have hs0013122 : InSquare (-71/320) (-21/64) (1/320) tau := by
                convert childUL hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0150.cell1207.sound htau (by
                simp only [Batch0150.cell1207, Batch0150.tau1207, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001312 | hy001312
            · have hs0013121 : InSquare (-69/320) (-107/320) (1/320) tau := by
                convert childLR hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0150.cell1206.sound htau (by
                simp only [Batch0150.cell1206, Batch0150.tau1206, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013121 (by positivity) using 1 <;> norm_num)
            · have hs0013123 : InSquare (-69/320) (-21/64) (1/320) tau := by
                convert childUR hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0151.cell1208.sound htau (by
                simp only [Batch0151.cell1208, Batch0151.tau1208, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy00131 | hy00131
        · have hs001311 : InSquare (-33/160) (-11/32) (1/160) tau := by
            convert childLR hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001311 | hx001311
          · rcases le_total tau.im (-11/32 : ℝ) with hy001311 | hy001311
            · have hs0013110 : InSquare (-67/320) (-111/320) (1/320) tau := by
                convert childLL hs001311 hx001311 hy001311 using 1 <;> norm_num
              exact (outside_0013110 htau hs0013110).elim
            · have hs0013112 : InSquare (-67/320) (-109/320) (1/320) tau := by
                convert childUL hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-67/320 : ℝ) with hx0013112 | hx0013112
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013112 | hy0013112
                · have hs00131120 : InSquare (-27/128) (-219/640) (1/640) tau := by
                    convert childLL hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2568.sound htau (by
                    simp only [Batch0321.cell2568, Batch0321.tau2568, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131120 (by positivity) using 1 <;> norm_num)
                · have hs00131122 : InSquare (-27/128) (-217/640) (1/640) tau := by
                    convert childUL hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2570.sound htau (by
                    simp only [Batch0321.cell2570, Batch0321.tau2570, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013112 | hy0013112
                · have hs00131121 : InSquare (-133/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2569.sound htau (by
                    simp only [Batch0321.cell2569, Batch0321.tau2569, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131121 (by positivity) using 1 <;> norm_num)
                · have hs00131123 : InSquare (-133/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2571.sound htau (by
                    simp only [Batch0321.cell2571, Batch0321.tau2571, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy001311 | hy001311
            · have hs0013111 : InSquare (-13/64) (-111/320) (1/320) tau := by
                convert childLR hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx0013111 | hx0013111
              · rcases le_total tau.im (-111/320 : ℝ) with hy0013111 | hy0013111
                · have hs00131110 : InSquare (-131/640) (-223/640) (1/640) tau := by
                    convert childLL hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact (outside_00131110 htau hs00131110).elim
                · have hs00131112 : InSquare (-131/640) (-221/640) (1/640) tau := by
                    convert childUL hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact Batch0320.cell2566.sound htau (by
                    simp only [Batch0320.cell2566, Batch0320.tau2566, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0013111 | hy0013111
                · have hs00131111 : InSquare (-129/640) (-223/640) (1/640) tau := by
                    convert childLR hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact (outside_00131111 htau hs00131111).elim
                · have hs00131113 : InSquare (-129/640) (-221/640) (1/640) tau := by
                    convert childUR hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact Batch0320.cell2567.sound htau (by
                    simp only [Batch0320.cell2567, Batch0320.tau2567, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131113 (by positivity) using 1 <;> norm_num)
            · have hs0013113 : InSquare (-13/64) (-109/320) (1/320) tau := by
                convert childUR hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx0013113 | hx0013113
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013113 | hy0013113
                · have hs00131130 : InSquare (-131/640) (-219/640) (1/640) tau := by
                    convert childLL hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2572.sound htau (by
                    simp only [Batch0321.cell2572, Batch0321.tau2572, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131130 (by positivity) using 1 <;> norm_num)
                · have hs00131132 : InSquare (-131/640) (-217/640) (1/640) tau := by
                    convert childUL hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2574.sound htau (by
                    simp only [Batch0321.cell2574, Batch0321.tau2574, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013113 | hy0013113
                · have hs00131131 : InSquare (-129/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2573.sound htau (by
                    simp only [Batch0321.cell2573, Batch0321.tau2573, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131131 (by positivity) using 1 <;> norm_num)
                · have hs00131133 : InSquare (-129/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2575.sound htau (by
                    simp only [Batch0321.cell2575, Batch0321.tau2575, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131133 (by positivity) using 1 <;> norm_num)
        · have hs001313 : InSquare (-33/160) (-53/160) (1/160) tau := by
            convert childUR hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001313 | hx001313
          · rcases le_total tau.im (-53/160 : ℝ) with hy001313 | hy001313
            · have hs0013130 : InSquare (-67/320) (-107/320) (1/320) tau := by
                convert childLL hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1209.sound htau (by
                simp only [Batch0151.cell1209, Batch0151.tau1209, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013130 (by positivity) using 1 <;> norm_num)
            · have hs0013132 : InSquare (-67/320) (-21/64) (1/320) tau := by
                convert childUL hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1211.sound htau (by
                simp only [Batch0151.cell1211, Batch0151.tau1211, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001313 | hy001313
            · have hs0013131 : InSquare (-13/64) (-107/320) (1/320) tau := by
                convert childLR hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1210.sound htau (by
                simp only [Batch0151.cell1210, Batch0151.tau1210, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013131 (by positivity) using 1 <;> norm_num)
            · have hs0013133 : InSquare (-13/64) (-21/64) (1/320) tau := by
                convert childUR hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1212.sound htau (by
                simp only [Batch0151.cell1212, Batch0151.tau1212, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013133 (by positivity) using 1 <;> norm_num)
    · have hs00133 : InSquare (-17/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00133 | hx00133
      · rcases le_total tau.im (-5/16 : ℝ) with hy00133 | hy00133
        · have hs001330 : InSquare (-7/32) (-51/160) (1/160) tau := by
            convert childLL hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001330 | hx001330
          · rcases le_total tau.im (-51/160 : ℝ) with hy001330 | hy001330
            · have hs0013300 : InSquare (-71/320) (-103/320) (1/320) tau := by
                convert childLL hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1228.sound htau (by
                simp only [Batch0153.cell1228, Batch0153.tau1228, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013300 (by positivity) using 1 <;> norm_num)
            · have hs0013302 : InSquare (-71/320) (-101/320) (1/320) tau := by
                convert childUL hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1230.sound htau (by
                simp only [Batch0153.cell1230, Batch0153.tau1230, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001330 | hy001330
            · have hs0013301 : InSquare (-69/320) (-103/320) (1/320) tau := by
                convert childLR hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1229.sound htau (by
                simp only [Batch0153.cell1229, Batch0153.tau1229, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013301 (by positivity) using 1 <;> norm_num)
            · have hs0013303 : InSquare (-69/320) (-101/320) (1/320) tau := by
                convert childUR hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1231.sound htau (by
                simp only [Batch0153.cell1231, Batch0153.tau1231, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013303 (by positivity) using 1 <;> norm_num)
        · have hs001332 : InSquare (-7/32) (-49/160) (1/160) tau := by
            convert childUL hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001332 | hx001332
          · rcases le_total tau.im (-49/160 : ℝ) with hy001332 | hy001332
            · have hs0013320 : InSquare (-71/320) (-99/320) (1/320) tau := by
                convert childLL hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1236.sound htau (by
                simp only [Batch0154.cell1236, Batch0154.tau1236, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013320 (by positivity) using 1 <;> norm_num)
            · have hs0013322 : InSquare (-71/320) (-97/320) (1/320) tau := by
                convert childUL hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1238.sound htau (by
                simp only [Batch0154.cell1238, Batch0154.tau1238, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001332 | hy001332
            · have hs0013321 : InSquare (-69/320) (-99/320) (1/320) tau := by
                convert childLR hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1237.sound htau (by
                simp only [Batch0154.cell1237, Batch0154.tau1237, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013321 (by positivity) using 1 <;> norm_num)
            · have hs0013323 : InSquare (-69/320) (-97/320) (1/320) tau := by
                convert childUR hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1239.sound htau (by
                simp only [Batch0154.cell1239, Batch0154.tau1239, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00133 | hy00133
        · have hs001331 : InSquare (-33/160) (-51/160) (1/160) tau := by
            convert childLR hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001331 | hx001331
          · rcases le_total tau.im (-51/160 : ℝ) with hy001331 | hy001331
            · have hs0013310 : InSquare (-67/320) (-103/320) (1/320) tau := by
                convert childLL hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1232.sound htau (by
                simp only [Batch0154.cell1232, Batch0154.tau1232, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013310 (by positivity) using 1 <;> norm_num)
            · have hs0013312 : InSquare (-67/320) (-101/320) (1/320) tau := by
                convert childUL hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1234.sound htau (by
                simp only [Batch0154.cell1234, Batch0154.tau1234, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001331 | hy001331
            · have hs0013311 : InSquare (-13/64) (-103/320) (1/320) tau := by
                convert childLR hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1233.sound htau (by
                simp only [Batch0154.cell1233, Batch0154.tau1233, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013311 (by positivity) using 1 <;> norm_num)
            · have hs0013313 : InSquare (-13/64) (-101/320) (1/320) tau := by
                convert childUR hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1235.sound htau (by
                simp only [Batch0154.cell1235, Batch0154.tau1235, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013313 (by positivity) using 1 <;> norm_num)
        · have hs001333 : InSquare (-33/160) (-49/160) (1/160) tau := by
            convert childUR hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001333 | hx001333
          · rcases le_total tau.im (-49/160 : ℝ) with hy001333 | hy001333
            · have hs0013330 : InSquare (-67/320) (-99/320) (1/320) tau := by
                convert childLL hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1240.sound htau (by
                simp only [Batch0155.cell1240, Batch0155.tau1240, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013330 (by positivity) using 1 <;> norm_num)
            · have hs0013332 : InSquare (-67/320) (-97/320) (1/320) tau := by
                convert childUL hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1242.sound htau (by
                simp only [Batch0155.cell1242, Batch0155.tau1242, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001333 | hy001333
            · have hs0013331 : InSquare (-13/64) (-99/320) (1/320) tau := by
                convert childLR hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1241.sound htau (by
                simp only [Batch0155.cell1241, Batch0155.tau1241, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013331 (by positivity) using 1 <;> norm_num)
            · have hs0013333 : InSquare (-13/64) (-97/320) (1/320) tau := by
                convert childUR hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1243.sound htau (by
                simp only [Batch0155.cell1243, Batch0155.tau1243, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_00210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/16) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (-21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (-43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (-41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (-17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0021 | hx0021
  · rcases le_total tau.im (-11/40 : ℝ) with hy0021 | hy0021
    · have hs00210 : InSquare (-27/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00210 htau hs00210).elim
    · have hs00212 : InSquare (-27/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00212 htau hs00212).elim
  · rcases le_total tau.im (-11/40 : ℝ) with hy0021 | hy0021
    · have hs00211 : InSquare (-5/16) (-23/80) (1/80) tau := by
        convert childLR hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00211 htau hs00211).elim
    · have hs00213 : InSquare (-5/16) (-21/80) (1/80) tau := by
        convert childUR hs hx0021 hy0021 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00213 | hx00213
      · rcases le_total tau.im (-21/80 : ℝ) with hy00213 | hy00213
        · have hs002130 : InSquare (-51/160) (-43/160) (1/160) tau := by
            convert childLL hs00213 hx00213 hy00213 using 1 <;> norm_num
          exact (outside_002130 htau hs002130).elim
        · have hs002132 : InSquare (-51/160) (-41/160) (1/160) tau := by
            convert childUL hs00213 hx00213 hy00213 using 1 <;> norm_num
          exact (outside_002132 htau hs002132).elim
      · rcases le_total tau.im (-21/80 : ℝ) with hy00213 | hy00213
        · have hs002131 : InSquare (-49/160) (-43/160) (1/160) tau := by
            convert childLR hs00213 hx00213 hy00213 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002131 | hx002131
          · rcases le_total tau.im (-43/160 : ℝ) with hy002131 | hy002131
            · have hs0021310 : InSquare (-99/320) (-87/320) (1/320) tau := by
                convert childLL hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021310 htau hs0021310).elim
            · have hs0021312 : InSquare (-99/320) (-17/64) (1/320) tau := by
                convert childUL hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021312 htau hs0021312).elim
          · rcases le_total tau.im (-43/160 : ℝ) with hy002131 | hy002131
            · have hs0021311 : InSquare (-97/320) (-87/320) (1/320) tau := by
                convert childLR hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021311 htau hs0021311).elim
            · have hs0021313 : InSquare (-97/320) (-17/64) (1/320) tau := by
                convert childUR hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact Batch0155.cell1244.sound htau (by
                simp only [Batch0155.cell1244, Batch0155.tau1244, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021313 (by positivity) using 1 <;> norm_num)
        · have hs002133 : InSquare (-49/160) (-41/160) (1/160) tau := by
            convert childUR hs00213 hx00213 hy00213 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002133 | hx002133
          · rcases le_total tau.im (-41/160 : ℝ) with hy002133 | hy002133
            · have hs0021330 : InSquare (-99/320) (-83/320) (1/320) tau := by
                convert childLL hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1245.sound htau (by
                simp only [Batch0155.cell1245, Batch0155.tau1245, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021330 (by positivity) using 1 <;> norm_num)
            · have hs0021332 : InSquare (-99/320) (-81/320) (1/320) tau := by
                convert childUL hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1247.sound htau (by
                simp only [Batch0155.cell1247, Batch0155.tau1247, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy002133 | hy002133
            · have hs0021331 : InSquare (-97/320) (-83/320) (1/320) tau := by
                convert childLR hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1246.sound htau (by
                simp only [Batch0155.cell1246, Batch0155.tau1246, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021331 (by positivity) using 1 <;> norm_num)
            · have hs0021333 : InSquare (-97/320) (-81/320) (1/320) tau := by
                convert childUR hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0156.cell1248.sound htau (by
                simp only [Batch0156.cell1248, Batch0156.tau1248, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_002300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/160) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (-37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (-15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (-73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-103/320) (-79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0023 | hx0023
  · rcases le_total tau.im (-9/40 : ℝ) with hy0023 | hy0023
    · have hs00230 : InSquare (-27/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx00230 | hx00230
      · rcases le_total tau.im (-19/80 : ℝ) with hy00230 | hy00230
        · have hs002300 : InSquare (-11/32) (-39/160) (1/160) tau := by
            convert childLL hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002300 htau hs002300).elim
        · have hs002302 : InSquare (-11/32) (-37/160) (1/160) tau := by
            convert childUL hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002302 htau hs002302).elim
      · rcases le_total tau.im (-19/80 : ℝ) with hy00230 | hy00230
        · have hs002301 : InSquare (-53/160) (-39/160) (1/160) tau := by
            convert childLR hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002301 htau hs002301).elim
        · have hs002303 : InSquare (-53/160) (-37/160) (1/160) tau := by
            convert childUR hs00230 hx00230 hy00230 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx002303 | hx002303
          · rcases le_total tau.im (-37/160 : ℝ) with hy002303 | hy002303
            · have hs0023030 : InSquare (-107/320) (-15/64) (1/320) tau := by
                convert childLL hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact (outside_0023030 htau hs0023030).elim
            · have hs0023032 : InSquare (-107/320) (-73/320) (1/320) tau := by
                convert childUL hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact (outside_0023032 htau hs0023032).elim
          · rcases le_total tau.im (-37/160 : ℝ) with hy002303 | hy002303
            · have hs0023031 : InSquare (-21/64) (-15/64) (1/320) tau := by
                convert childLR hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact Batch0156.cell1249.sound htau (by
                simp only [Batch0156.cell1249, Batch0156.tau1249, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023031 (by positivity) using 1 <;> norm_num)
            · have hs0023033 : InSquare (-21/64) (-73/320) (1/320) tau := by
                convert childUR hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact Batch0156.cell1250.sound htau (by
                simp only [Batch0156.cell1250, Batch0156.tau1250, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023033 (by positivity) using 1 <;> norm_num)
    · have hs00232 : InSquare (-27/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx00232 | hx00232
      · rcases le_total tau.im (-17/80 : ℝ) with hy00232 | hy00232
        · have hs002320 : InSquare (-11/32) (-7/32) (1/160) tau := by
            convert childLL hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx002320 | hx002320
          · rcases le_total tau.im (-7/32 : ℝ) with hy002320 | hy002320
            · have hs0023200 : InSquare (-111/320) (-71/320) (1/320) tau := by
                convert childLL hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023200 htau hs0023200).elim
            · have hs0023202 : InSquare (-111/320) (-69/320) (1/320) tau := by
                convert childUL hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023202 htau hs0023202).elim
          · rcases le_total tau.im (-7/32 : ℝ) with hy002320 | hy002320
            · have hs0023201 : InSquare (-109/320) (-71/320) (1/320) tau := by
                convert childLR hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023201 htau hs0023201).elim
            · have hs0023203 : InSquare (-109/320) (-69/320) (1/320) tau := by
                convert childUR hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact Batch0157.cell1262.sound htau (by
                simp only [Batch0157.cell1262, Batch0157.tau1262, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023203 (by positivity) using 1 <;> norm_num)
        · have hs002322 : InSquare (-11/32) (-33/160) (1/160) tau := by
            convert childUL hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx002322 | hx002322
          · rcases le_total tau.im (-33/160 : ℝ) with hy002322 | hy002322
            · have hs0023220 : InSquare (-111/320) (-67/320) (1/320) tau := by
                convert childLL hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact (outside_0023220 htau hs0023220).elim
            · have hs0023222 : InSquare (-111/320) (-13/64) (1/320) tau := by
                convert childUL hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1268.sound htau (by
                simp only [Batch0158.cell1268, Batch0158.tau1268, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-33/160 : ℝ) with hy002322 | hy002322
            · have hs0023221 : InSquare (-109/320) (-67/320) (1/320) tau := by
                convert childLR hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1267.sound htau (by
                simp only [Batch0158.cell1267, Batch0158.tau1267, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023221 (by positivity) using 1 <;> norm_num)
            · have hs0023223 : InSquare (-109/320) (-13/64) (1/320) tau := by
                convert childUR hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1269.sound htau (by
                simp only [Batch0158.cell1269, Batch0158.tau1269, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00232 | hy00232
        · have hs002321 : InSquare (-53/160) (-7/32) (1/160) tau := by
            convert childLR hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx002321 | hx002321
          · rcases le_total tau.im (-7/32 : ℝ) with hy002321 | hy002321
            · have hs0023210 : InSquare (-107/320) (-71/320) (1/320) tau := by
                convert childLL hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0157.cell1263.sound htau (by
                simp only [Batch0157.cell1263, Batch0157.tau1263, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023210 (by positivity) using 1 <;> norm_num)
            · have hs0023212 : InSquare (-107/320) (-69/320) (1/320) tau := by
                convert childUL hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1265.sound htau (by
                simp only [Batch0158.cell1265, Batch0158.tau1265, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy002321 | hy002321
            · have hs0023211 : InSquare (-21/64) (-71/320) (1/320) tau := by
                convert childLR hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1264.sound htau (by
                simp only [Batch0158.cell1264, Batch0158.tau1264, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023211 (by positivity) using 1 <;> norm_num)
            · have hs0023213 : InSquare (-21/64) (-69/320) (1/320) tau := by
                convert childUR hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1266.sound htau (by
                simp only [Batch0158.cell1266, Batch0158.tau1266, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023213 (by positivity) using 1 <;> norm_num)
        · have hs002323 : InSquare (-53/160) (-33/160) (1/160) tau := by
            convert childUR hs00232 hx00232 hy00232 using 1 <;> norm_num
          exact Batch0043.cell0345.sound htau (by
            simp only [Batch0043.cell0345, Batch0043.tau0345, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0023 | hy0023
    · have hs00231 : InSquare (-5/16) (-19/80) (1/80) tau := by
        convert childLR hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00231 | hx00231
      · rcases le_total tau.im (-19/80 : ℝ) with hy00231 | hy00231
        · have hs002310 : InSquare (-51/160) (-39/160) (1/160) tau := by
            convert childLL hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx002310 | hx002310
          · rcases le_total tau.im (-39/160 : ℝ) with hy002310 | hy002310
            · have hs0023100 : InSquare (-103/320) (-79/320) (1/320) tau := by
                convert childLL hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact (outside_0023100 htau hs0023100).elim
            · have hs0023102 : InSquare (-103/320) (-77/320) (1/320) tau := by
                convert childUL hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1252.sound htau (by
                simp only [Batch0156.cell1252, Batch0156.tau1252, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy002310 | hy002310
            · have hs0023101 : InSquare (-101/320) (-79/320) (1/320) tau := by
                convert childLR hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1251.sound htau (by
                simp only [Batch0156.cell1251, Batch0156.tau1251, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023101 (by positivity) using 1 <;> norm_num)
            · have hs0023103 : InSquare (-101/320) (-77/320) (1/320) tau := by
                convert childUR hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1253.sound htau (by
                simp only [Batch0156.cell1253, Batch0156.tau1253, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023103 (by positivity) using 1 <;> norm_num)
        · have hs002312 : InSquare (-51/160) (-37/160) (1/160) tau := by
            convert childUL hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx002312 | hx002312
          · rcases le_total tau.im (-37/160 : ℝ) with hy002312 | hy002312
            · have hs0023120 : InSquare (-103/320) (-15/64) (1/320) tau := by
                convert childLL hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1258.sound htau (by
                simp only [Batch0157.cell1258, Batch0157.tau1258, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023120 (by positivity) using 1 <;> norm_num)
            · have hs0023122 : InSquare (-103/320) (-73/320) (1/320) tau := by
                convert childUL hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1260.sound htau (by
                simp only [Batch0157.cell1260, Batch0157.tau1260, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy002312 | hy002312
            · have hs0023121 : InSquare (-101/320) (-15/64) (1/320) tau := by
                convert childLR hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1259.sound htau (by
                simp only [Batch0157.cell1259, Batch0157.tau1259, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023121 (by positivity) using 1 <;> norm_num)
            · have hs0023123 : InSquare (-101/320) (-73/320) (1/320) tau := by
                convert childUR hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1261.sound htau (by
                simp only [Batch0157.cell1261, Batch0157.tau1261, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00231 | hy00231
        · have hs002311 : InSquare (-49/160) (-39/160) (1/160) tau := by
            convert childLR hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002311 | hx002311
          · rcases le_total tau.im (-39/160 : ℝ) with hy002311 | hy002311
            · have hs0023110 : InSquare (-99/320) (-79/320) (1/320) tau := by
                convert childLL hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0156.cell1254.sound htau (by
                simp only [Batch0156.cell1254, Batch0156.tau1254, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023110 (by positivity) using 1 <;> norm_num)
            · have hs0023112 : InSquare (-99/320) (-77/320) (1/320) tau := by
                convert childUL hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0157.cell1256.sound htau (by
                simp only [Batch0157.cell1256, Batch0157.tau1256, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy002311 | hy002311
            · have hs0023111 : InSquare (-97/320) (-79/320) (1/320) tau := by
                convert childLR hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0156.cell1255.sound htau (by
                simp only [Batch0156.cell1255, Batch0156.tau1255, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023111 (by positivity) using 1 <;> norm_num)
            · have hs0023113 : InSquare (-97/320) (-77/320) (1/320) tau := by
                convert childUR hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0157.cell1257.sound htau (by
                simp only [Batch0157.cell1257, Batch0157.tau1257, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023113 (by positivity) using 1 <;> norm_num)
        · have hs002313 : InSquare (-49/160) (-37/160) (1/160) tau := by
            convert childUR hs00231 hx00231 hy00231 using 1 <;> norm_num
          exact Batch0043.cell0344.sound htau (by
            simp only [Batch0043.cell0344, Batch0043.tau0344, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002313 (by positivity) using 1 <;> norm_num)
    · have hs00233 : InSquare (-5/16) (-17/80) (1/80) tau := by
        convert childUR hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00233 | hx00233
      · rcases le_total tau.im (-17/80 : ℝ) with hy00233 | hy00233
        · have hs002330 : InSquare (-51/160) (-7/32) (1/160) tau := by
            convert childLL hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0346.sound htau (by
            simp only [Batch0043.cell0346, Batch0043.tau0346, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002330 (by positivity) using 1 <;> norm_num)
        · have hs002332 : InSquare (-51/160) (-33/160) (1/160) tau := by
            convert childUL hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0348.sound htau (by
            simp only [Batch0043.cell0348, Batch0043.tau0348, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00233 | hy00233
        · have hs002331 : InSquare (-49/160) (-7/32) (1/160) tau := by
            convert childLR hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0347.sound htau (by
            simp only [Batch0043.cell0347, Batch0043.tau0347, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002331 (by positivity) using 1 <;> norm_num)
        · have hs002333 : InSquare (-49/160) (-33/160) (1/160) tau := by
            convert childUR hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0349.sound htau (by
            simp only [Batch0043.cell0349, Batch0043.tau0349, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_003000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/160) (-47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (-93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-93/320) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (-89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0030 | hx0030
  · rcases le_total tau.im (-11/40 : ℝ) with hy0030 | hy0030
    · have hs00300 : InSquare (-23/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00300 | hx00300
      · rcases le_total tau.im (-23/80 : ℝ) with hy00300 | hy00300
        · have hs003000 : InSquare (-47/160) (-47/160) (1/160) tau := by
            convert childLL hs00300 hx00300 hy00300 using 1 <;> norm_num
          exact (outside_003000 htau hs003000).elim
        · have hs003002 : InSquare (-47/160) (-9/32) (1/160) tau := by
            convert childUL hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003002 | hx003002
          · rcases le_total tau.im (-9/32 : ℝ) with hy003002 | hy003002
            · have hs0030020 : InSquare (-19/64) (-91/320) (1/320) tau := by
                convert childLL hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030020 htau hs0030020).elim
            · have hs0030022 : InSquare (-19/64) (-89/320) (1/320) tau := by
                convert childUL hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030022 htau hs0030022).elim
          · rcases le_total tau.im (-9/32 : ℝ) with hy003002 | hy003002
            · have hs0030021 : InSquare (-93/320) (-91/320) (1/320) tau := by
                convert childLR hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030021 htau hs0030021).elim
            · have hs0030023 : InSquare (-93/320) (-89/320) (1/320) tau := by
                convert childUR hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact Batch0158.cell1271.sound htau (by
                simp only [Batch0158.cell1271, Batch0158.tau1271, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00300 | hy00300
        · have hs003001 : InSquare (-9/32) (-47/160) (1/160) tau := by
            convert childLR hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003001 | hx003001
          · rcases le_total tau.im (-47/160 : ℝ) with hy003001 | hy003001
            · have hs0030010 : InSquare (-91/320) (-19/64) (1/320) tau := by
                convert childLL hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030010 htau hs0030010).elim
            · have hs0030012 : InSquare (-91/320) (-93/320) (1/320) tau := by
                convert childUL hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030012 htau hs0030012).elim
          · rcases le_total tau.im (-47/160 : ℝ) with hy003001 | hy003001
            · have hs0030011 : InSquare (-89/320) (-19/64) (1/320) tau := by
                convert childLR hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030011 htau hs0030011).elim
            · have hs0030013 : InSquare (-89/320) (-93/320) (1/320) tau := by
                convert childUR hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact Batch0158.cell1270.sound htau (by
                simp only [Batch0158.cell1270, Batch0158.tau1270, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030013 (by positivity) using 1 <;> norm_num)
        · have hs003003 : InSquare (-9/32) (-9/32) (1/160) tau := by
            convert childUR hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003003 | hx003003
          · rcases le_total tau.im (-9/32 : ℝ) with hy003003 | hy003003
            · have hs0030030 : InSquare (-91/320) (-91/320) (1/320) tau := by
                convert childLL hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1272.sound htau (by
                simp only [Batch0159.cell1272, Batch0159.tau1272, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030030 (by positivity) using 1 <;> norm_num)
            · have hs0030032 : InSquare (-91/320) (-89/320) (1/320) tau := by
                convert childUL hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1274.sound htau (by
                simp only [Batch0159.cell1274, Batch0159.tau1274, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003003 | hy003003
            · have hs0030031 : InSquare (-89/320) (-91/320) (1/320) tau := by
                convert childLR hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1273.sound htau (by
                simp only [Batch0159.cell1273, Batch0159.tau1273, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030031 (by positivity) using 1 <;> norm_num)
            · have hs0030033 : InSquare (-89/320) (-89/320) (1/320) tau := by
                convert childUR hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1275.sound htau (by
                simp only [Batch0159.cell1275, Batch0159.tau1275, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030033 (by positivity) using 1 <;> norm_num)
    · have hs00302 : InSquare (-23/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00302 | hx00302
      · rcases le_total tau.im (-21/80 : ℝ) with hy00302 | hy00302
        · have hs003020 : InSquare (-47/160) (-43/160) (1/160) tau := by
            convert childLL hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003020 | hx003020
          · rcases le_total tau.im (-43/160 : ℝ) with hy003020 | hy003020
            · have hs0030200 : InSquare (-19/64) (-87/320) (1/320) tau := by
                convert childLL hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1292.sound htau (by
                simp only [Batch0161.cell1292, Batch0161.tau1292, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030200 (by positivity) using 1 <;> norm_num)
            · have hs0030202 : InSquare (-19/64) (-17/64) (1/320) tau := by
                convert childUL hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1294.sound htau (by
                simp only [Batch0161.cell1294, Batch0161.tau1294, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003020 | hy003020
            · have hs0030201 : InSquare (-93/320) (-87/320) (1/320) tau := by
                convert childLR hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1293.sound htau (by
                simp only [Batch0161.cell1293, Batch0161.tau1293, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030201 (by positivity) using 1 <;> norm_num)
            · have hs0030203 : InSquare (-93/320) (-17/64) (1/320) tau := by
                convert childUR hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1295.sound htau (by
                simp only [Batch0161.cell1295, Batch0161.tau1295, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030203 (by positivity) using 1 <;> norm_num)
        · have hs003022 : InSquare (-47/160) (-41/160) (1/160) tau := by
            convert childUL hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003022 | hx003022
          · rcases le_total tau.im (-41/160 : ℝ) with hy003022 | hy003022
            · have hs0030220 : InSquare (-19/64) (-83/320) (1/320) tau := by
                convert childLL hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1300.sound htau (by
                simp only [Batch0162.cell1300, Batch0162.tau1300, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030220 (by positivity) using 1 <;> norm_num)
            · have hs0030222 : InSquare (-19/64) (-81/320) (1/320) tau := by
                convert childUL hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1302.sound htau (by
                simp only [Batch0162.cell1302, Batch0162.tau1302, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy003022 | hy003022
            · have hs0030221 : InSquare (-93/320) (-83/320) (1/320) tau := by
                convert childLR hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1301.sound htau (by
                simp only [Batch0162.cell1301, Batch0162.tau1301, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030221 (by positivity) using 1 <;> norm_num)
            · have hs0030223 : InSquare (-93/320) (-81/320) (1/320) tau := by
                convert childUR hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1303.sound htau (by
                simp only [Batch0162.cell1303, Batch0162.tau1303, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00302 | hy00302
        · have hs003021 : InSquare (-9/32) (-43/160) (1/160) tau := by
            convert childLR hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003021 | hx003021
          · rcases le_total tau.im (-43/160 : ℝ) with hy003021 | hy003021
            · have hs0030210 : InSquare (-91/320) (-87/320) (1/320) tau := by
                convert childLL hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1296.sound htau (by
                simp only [Batch0162.cell1296, Batch0162.tau1296, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030210 (by positivity) using 1 <;> norm_num)
            · have hs0030212 : InSquare (-91/320) (-17/64) (1/320) tau := by
                convert childUL hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1298.sound htau (by
                simp only [Batch0162.cell1298, Batch0162.tau1298, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003021 | hy003021
            · have hs0030211 : InSquare (-89/320) (-87/320) (1/320) tau := by
                convert childLR hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1297.sound htau (by
                simp only [Batch0162.cell1297, Batch0162.tau1297, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030211 (by positivity) using 1 <;> norm_num)
            · have hs0030213 : InSquare (-89/320) (-17/64) (1/320) tau := by
                convert childUR hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1299.sound htau (by
                simp only [Batch0162.cell1299, Batch0162.tau1299, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030213 (by positivity) using 1 <;> norm_num)
        · have hs003023 : InSquare (-9/32) (-41/160) (1/160) tau := by
            convert childUR hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003023 | hx003023
          · rcases le_total tau.im (-41/160 : ℝ) with hy003023 | hy003023
            · have hs0030230 : InSquare (-91/320) (-83/320) (1/320) tau := by
                convert childLL hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1304.sound htau (by
                simp only [Batch0163.cell1304, Batch0163.tau1304, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030230 (by positivity) using 1 <;> norm_num)
            · have hs0030232 : InSquare (-91/320) (-81/320) (1/320) tau := by
                convert childUL hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1306.sound htau (by
                simp only [Batch0163.cell1306, Batch0163.tau1306, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy003023 | hy003023
            · have hs0030231 : InSquare (-89/320) (-83/320) (1/320) tau := by
                convert childLR hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1305.sound htau (by
                simp only [Batch0163.cell1305, Batch0163.tau1305, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030231 (by positivity) using 1 <;> norm_num)
            · have hs0030233 : InSquare (-89/320) (-81/320) (1/320) tau := by
                convert childUR hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1307.sound htau (by
                simp only [Batch0163.cell1307, Batch0163.tau1307, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0030 | hy0030
    · have hs00301 : InSquare (-21/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00301 | hx00301
      · rcases le_total tau.im (-23/80 : ℝ) with hy00301 | hy00301
        · have hs003010 : InSquare (-43/160) (-47/160) (1/160) tau := by
            convert childLL hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003010 | hx003010
          · rcases le_total tau.im (-47/160 : ℝ) with hy003010 | hy003010
            · have hs0030100 : InSquare (-87/320) (-19/64) (1/320) tau := by
                convert childLL hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1276.sound htau (by
                simp only [Batch0159.cell1276, Batch0159.tau1276, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030100 (by positivity) using 1 <;> norm_num)
            · have hs0030102 : InSquare (-87/320) (-93/320) (1/320) tau := by
                convert childUL hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1278.sound htau (by
                simp only [Batch0159.cell1278, Batch0159.tau1278, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003010 | hy003010
            · have hs0030101 : InSquare (-17/64) (-19/64) (1/320) tau := by
                convert childLR hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1277.sound htau (by
                simp only [Batch0159.cell1277, Batch0159.tau1277, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030101 (by positivity) using 1 <;> norm_num)
            · have hs0030103 : InSquare (-17/64) (-93/320) (1/320) tau := by
                convert childUR hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1279.sound htau (by
                simp only [Batch0159.cell1279, Batch0159.tau1279, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030103 (by positivity) using 1 <;> norm_num)
        · have hs003012 : InSquare (-43/160) (-9/32) (1/160) tau := by
            convert childUL hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003012 | hx003012
          · rcases le_total tau.im (-9/32 : ℝ) with hy003012 | hy003012
            · have hs0030120 : InSquare (-87/320) (-91/320) (1/320) tau := by
                convert childLL hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1284.sound htau (by
                simp only [Batch0160.cell1284, Batch0160.tau1284, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030120 (by positivity) using 1 <;> norm_num)
            · have hs0030122 : InSquare (-87/320) (-89/320) (1/320) tau := by
                convert childUL hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1286.sound htau (by
                simp only [Batch0160.cell1286, Batch0160.tau1286, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003012 | hy003012
            · have hs0030121 : InSquare (-17/64) (-91/320) (1/320) tau := by
                convert childLR hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1285.sound htau (by
                simp only [Batch0160.cell1285, Batch0160.tau1285, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030121 (by positivity) using 1 <;> norm_num)
            · have hs0030123 : InSquare (-17/64) (-89/320) (1/320) tau := by
                convert childUR hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1287.sound htau (by
                simp only [Batch0160.cell1287, Batch0160.tau1287, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00301 | hy00301
        · have hs003011 : InSquare (-41/160) (-47/160) (1/160) tau := by
            convert childLR hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003011 | hx003011
          · rcases le_total tau.im (-47/160 : ℝ) with hy003011 | hy003011
            · have hs0030110 : InSquare (-83/320) (-19/64) (1/320) tau := by
                convert childLL hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1280.sound htau (by
                simp only [Batch0160.cell1280, Batch0160.tau1280, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030110 (by positivity) using 1 <;> norm_num)
            · have hs0030112 : InSquare (-83/320) (-93/320) (1/320) tau := by
                convert childUL hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1282.sound htau (by
                simp only [Batch0160.cell1282, Batch0160.tau1282, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003011 | hy003011
            · have hs0030111 : InSquare (-81/320) (-19/64) (1/320) tau := by
                convert childLR hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1281.sound htau (by
                simp only [Batch0160.cell1281, Batch0160.tau1281, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030111 (by positivity) using 1 <;> norm_num)
            · have hs0030113 : InSquare (-81/320) (-93/320) (1/320) tau := by
                convert childUR hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1283.sound htau (by
                simp only [Batch0160.cell1283, Batch0160.tau1283, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030113 (by positivity) using 1 <;> norm_num)
        · have hs003013 : InSquare (-41/160) (-9/32) (1/160) tau := by
            convert childUR hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003013 | hx003013
          · rcases le_total tau.im (-9/32 : ℝ) with hy003013 | hy003013
            · have hs0030130 : InSquare (-83/320) (-91/320) (1/320) tau := by
                convert childLL hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1288.sound htau (by
                simp only [Batch0161.cell1288, Batch0161.tau1288, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030130 (by positivity) using 1 <;> norm_num)
            · have hs0030132 : InSquare (-83/320) (-89/320) (1/320) tau := by
                convert childUL hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1290.sound htau (by
                simp only [Batch0161.cell1290, Batch0161.tau1290, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003013 | hy003013
            · have hs0030131 : InSquare (-81/320) (-91/320) (1/320) tau := by
                convert childLR hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1289.sound htau (by
                simp only [Batch0161.cell1289, Batch0161.tau1289, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030131 (by positivity) using 1 <;> norm_num)
            · have hs0030133 : InSquare (-81/320) (-89/320) (1/320) tau := by
                convert childUR hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1291.sound htau (by
                simp only [Batch0161.cell1291, Batch0161.tau1291, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030133 (by positivity) using 1 <;> norm_num)
    · have hs00303 : InSquare (-21/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00303 | hx00303
      · rcases le_total tau.im (-21/80 : ℝ) with hy00303 | hy00303
        · have hs003030 : InSquare (-43/160) (-43/160) (1/160) tau := by
            convert childLL hs00303 hx00303 hy00303 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003030 | hx003030
          · rcases le_total tau.im (-43/160 : ℝ) with hy003030 | hy003030
            · have hs0030300 : InSquare (-87/320) (-87/320) (1/320) tau := by
                convert childLL hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1308.sound htau (by
                simp only [Batch0163.cell1308, Batch0163.tau1308, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030300 (by positivity) using 1 <;> norm_num)
            · have hs0030302 : InSquare (-87/320) (-17/64) (1/320) tau := by
                convert childUL hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1310.sound htau (by
                simp only [Batch0163.cell1310, Batch0163.tau1310, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003030 | hy003030
            · have hs0030301 : InSquare (-17/64) (-87/320) (1/320) tau := by
                convert childLR hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1309.sound htau (by
                simp only [Batch0163.cell1309, Batch0163.tau1309, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030301 (by positivity) using 1 <;> norm_num)
            · have hs0030303 : InSquare (-17/64) (-17/64) (1/320) tau := by
                convert childUR hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1311.sound htau (by
                simp only [Batch0163.cell1311, Batch0163.tau1311, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030303 (by positivity) using 1 <;> norm_num)
        · have hs003032 : InSquare (-43/160) (-41/160) (1/160) tau := by
            convert childUL hs00303 hx00303 hy00303 using 1 <;> norm_num
          exact Batch0043.cell0350.sound htau (by
            simp only [Batch0043.cell0350, Batch0043.tau0350, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00303 | hy00303
        · have hs003031 : InSquare (-41/160) (-43/160) (1/160) tau := by
            convert childLR hs00303 hx00303 hy00303 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003031 | hx003031
          · rcases le_total tau.im (-43/160 : ℝ) with hy003031 | hy003031
            · have hs0030310 : InSquare (-83/320) (-87/320) (1/320) tau := by
                convert childLL hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1312.sound htau (by
                simp only [Batch0164.cell1312, Batch0164.tau1312, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030310 (by positivity) using 1 <;> norm_num)
            · have hs0030312 : InSquare (-83/320) (-17/64) (1/320) tau := by
                convert childUL hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1314.sound htau (by
                simp only [Batch0164.cell1314, Batch0164.tau1314, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003031 | hy003031
            · have hs0030311 : InSquare (-81/320) (-87/320) (1/320) tau := by
                convert childLR hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1313.sound htau (by
                simp only [Batch0164.cell1313, Batch0164.tau1313, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030311 (by positivity) using 1 <;> norm_num)
            · have hs0030313 : InSquare (-81/320) (-17/64) (1/320) tau := by
                convert childUR hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1315.sound htau (by
                simp only [Batch0164.cell1315, Batch0164.tau1315, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030313 (by positivity) using 1 <;> norm_num)
        · have hs003033 : InSquare (-41/160) (-41/160) (1/160) tau := by
            convert childUR hs00303 hx00303 hy00303 using 1 <;> norm_num
          exact Batch0043.cell0351.sound htau (by
            simp only [Batch0043.cell0351, Batch0043.tau0351, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030

end


