-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3103__11
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage3103__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:35.238689+00:00
-- url     : https://prove2.me/theorems/9a83dbfb-1d44-4afa-a646-8ee5e0e9f29c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110, GeneralCK.Certifi…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103 (+10 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3103 (+10 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3110, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3111, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3112, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3113, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3120, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3121, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3122, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3123, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3130, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage3131).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0040
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0126
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0129
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3103 | hx3103
  · rcases le_total tau.im (3/40 : ℝ) with hy3103 | hy3103
    · have hs31030 : InSquare (21/80) (1/16) (1/80) tau := by
        convert childLL hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0036.cell0295.sound htau (by
        simp only [Batch0036.cell0295, Batch0036.tau0295, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31030 (by positivity) using 1 <;> norm_num)
    · have hs31032 : InSquare (21/80) (7/80) (1/80) tau := by
        convert childUL hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0297.sound htau (by
        simp only [Batch0037.cell0297, Batch0037.tau0297, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3103 | hy3103
    · have hs31031 : InSquare (23/80) (1/16) (1/80) tau := by
        convert childLR hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0296.sound htau (by
        simp only [Batch0037.cell0296, Batch0037.tau0296, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31031 (by positivity) using 1 <;> norm_num)
    · have hs31033 : InSquare (23/80) (7/80) (1/80) tau := by
        convert childUR hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0298.sound htau (by
        simp only [Batch0037.cell0298, Batch0037.tau0298, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3110 | hx3110
  · rcases le_total tau.im (1/40 : ℝ) with hy3110 | hy3110
    · have hs31100 : InSquare (5/16) (1/80) (1/80) tau := by
        convert childLL hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0299.sound htau (by
        simp only [Batch0037.cell0299, Batch0037.tau0299, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31100 (by positivity) using 1 <;> norm_num)
    · have hs31102 : InSquare (5/16) (3/80) (1/80) tau := by
        convert childUL hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0301.sound htau (by
        simp only [Batch0037.cell0301, Batch0037.tau0301, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3110 | hy3110
    · have hs31101 : InSquare (27/80) (1/80) (1/80) tau := by
        convert childLR hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0300.sound htau (by
        simp only [Batch0037.cell0300, Batch0037.tau0300, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31101 (by positivity) using 1 <;> norm_num)
    · have hs31103 : InSquare (27/80) (3/80) (1/80) tau := by
        convert childUR hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0302.sound htau (by
        simp only [Batch0037.cell0302, Batch0037.tau0302, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3111 | hx3111
  · rcases le_total tau.im (1/40 : ℝ) with hy3111 | hy3111
    · have hs31110 : InSquare (29/80) (1/80) (1/80) tau := by
        convert childLL hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0037.cell0303.sound htau (by
        simp only [Batch0037.cell0303, Batch0037.tau0303, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31110 (by positivity) using 1 <;> norm_num)
    · have hs31112 : InSquare (29/80) (3/80) (1/80) tau := by
        convert childUL hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0038.cell0305.sound htau (by
        simp only [Batch0038.cell0305, Batch0038.tau0305, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3111 | hy3111
    · have hs31111 : InSquare (31/80) (1/80) (1/80) tau := by
        convert childLR hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0038.cell0304.sound htau (by
        simp only [Batch0038.cell0304, Batch0038.tau0304, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31111 (by positivity) using 1 <;> norm_num)
    · have hs31113 : InSquare (31/80) (3/80) (1/80) tau := by
        convert childUR hs hx3111 hy3111 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31113 | hx31113
      · rcases le_total tau.im (3/80 : ℝ) with hy31113 | hy31113
        · have hs311130 : InSquare (61/160) (1/32) (1/160) tau := by
            convert childLL hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0986.sound htau (by
            simp only [Batch0123.cell0986, Batch0123.tau0986, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311130 (by positivity) using 1 <;> norm_num)
        · have hs311132 : InSquare (61/160) (7/160) (1/160) tau := by
            convert childUL hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0988.sound htau (by
            simp only [Batch0123.cell0988, Batch0123.tau0988, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/80 : ℝ) with hy31113 | hy31113
        · have hs311131 : InSquare (63/160) (1/32) (1/160) tau := by
            convert childLR hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0987.sound htau (by
            simp only [Batch0123.cell0987, Batch0123.tau0987, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311131 (by positivity) using 1 <;> norm_num)
        · have hs311133 : InSquare (63/160) (7/160) (1/160) tau := by
            convert childUR hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0989.sound htau (by
            simp only [Batch0123.cell0989, Batch0123.tau0989, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3112 | hx3112
  · rcases le_total tau.im (3/40 : ℝ) with hy3112 | hy3112
    · have hs31120 : InSquare (5/16) (1/16) (1/80) tau := by
        convert childLL hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0306.sound htau (by
        simp only [Batch0038.cell0306, Batch0038.tau0306, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31120 (by positivity) using 1 <;> norm_num)
    · have hs31122 : InSquare (5/16) (7/80) (1/80) tau := by
        convert childUL hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0308.sound htau (by
        simp only [Batch0038.cell0308, Batch0038.tau0308, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3112 | hy3112
    · have hs31121 : InSquare (27/80) (1/16) (1/80) tau := by
        convert childLR hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0307.sound htau (by
        simp only [Batch0038.cell0307, Batch0038.tau0307, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31121 (by positivity) using 1 <;> norm_num)
    · have hs31123 : InSquare (27/80) (7/80) (1/80) tau := by
        convert childUR hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0309.sound htau (by
        simp only [Batch0038.cell0309, Batch0038.tau0309, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3113 | hx3113
  · rcases le_total tau.im (3/40 : ℝ) with hy3113 | hy3113
    · have hs31130 : InSquare (29/80) (1/16) (1/80) tau := by
        convert childLL hs hx3113 hy3113 using 1 <;> norm_num
      exact Batch0038.cell0310.sound htau (by
        simp only [Batch0038.cell0310, Batch0038.tau0310, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31130 (by positivity) using 1 <;> norm_num)
    · have hs31132 : InSquare (29/80) (7/80) (1/80) tau := by
        convert childUL hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31132 | hx31132
      · rcases le_total tau.im (7/80 : ℝ) with hy31132 | hy31132
        · have hs311320 : InSquare (57/160) (13/160) (1/160) tau := by
            convert childLL hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0994.sound htau (by
            simp only [Batch0124.cell0994, Batch0124.tau0994, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311320 (by positivity) using 1 <;> norm_num)
        · have hs311322 : InSquare (57/160) (3/32) (1/160) tau := by
            convert childUL hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0996.sound htau (by
            simp only [Batch0124.cell0996, Batch0124.tau0996, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy31132 | hy31132
        · have hs311321 : InSquare (59/160) (13/160) (1/160) tau := by
            convert childLR hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0995.sound htau (by
            simp only [Batch0124.cell0995, Batch0124.tau0995, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311321 (by positivity) using 1 <;> norm_num)
        · have hs311323 : InSquare (59/160) (3/32) (1/160) tau := by
            convert childUR hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0997.sound htau (by
            simp only [Batch0124.cell0997, Batch0124.tau0997, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3113 | hy3113
    · have hs31131 : InSquare (31/80) (1/16) (1/80) tau := by
        convert childLR hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31131 | hx31131
      · rcases le_total tau.im (1/16 : ℝ) with hy31131 | hy31131
        · have hs311310 : InSquare (61/160) (9/160) (1/160) tau := by
            convert childLL hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0123.cell0990.sound htau (by
            simp only [Batch0123.cell0990, Batch0123.tau0990, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311310 (by positivity) using 1 <;> norm_num)
        · have hs311312 : InSquare (61/160) (11/160) (1/160) tau := by
            convert childUL hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0124.cell0992.sound htau (by
            simp only [Batch0124.cell0992, Batch0124.tau0992, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (1/16 : ℝ) with hy31131 | hy31131
        · have hs311311 : InSquare (63/160) (9/160) (1/160) tau := by
            convert childLR hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0123.cell0991.sound htau (by
            simp only [Batch0123.cell0991, Batch0123.tau0991, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311311 (by positivity) using 1 <;> norm_num)
        · have hs311313 : InSquare (63/160) (11/160) (1/160) tau := by
            convert childUR hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0124.cell0993.sound htau (by
            simp only [Batch0124.cell0993, Batch0124.tau0993, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311313 (by positivity) using 1 <;> norm_num)
    · have hs31133 : InSquare (31/80) (7/80) (1/80) tau := by
        convert childUR hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31133 | hx31133
      · rcases le_total tau.im (7/80 : ℝ) with hy31133 | hy31133
        · have hs311330 : InSquare (61/160) (13/160) (1/160) tau := by
            convert childLL hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0124.cell0998.sound htau (by
            simp only [Batch0124.cell0998, Batch0124.tau0998, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311330 (by positivity) using 1 <;> norm_num)
        · have hs311332 : InSquare (61/160) (3/32) (1/160) tau := by
            convert childUL hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0125.cell1000.sound htau (by
            simp only [Batch0125.cell1000, Batch0125.tau1000, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy31133 | hy31133
        · have hs311331 : InSquare (63/160) (13/160) (1/160) tau := by
            convert childLR hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0124.cell0999.sound htau (by
            simp only [Batch0124.cell0999, Batch0124.tau0999, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311331 (by positivity) using 1 <;> norm_num)
        · have hs311333 : InSquare (63/160) (3/32) (1/160) tau := by
            convert childUR hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0125.cell1001.sound htau (by
            simp only [Batch0125.cell1001, Batch0125.tau1001, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3120 | hx3120
  · rcases le_total tau.im (1/8 : ℝ) with hy3120 | hy3120
    · have hs31200 : InSquare (17/80) (9/80) (1/80) tau := by
        convert childLL hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0038.cell0311.sound htau (by
        simp only [Batch0038.cell0311, Batch0038.tau0311, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31200 (by positivity) using 1 <;> norm_num)
    · have hs31202 : InSquare (17/80) (11/80) (1/80) tau := by
        convert childUL hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0313.sound htau (by
        simp only [Batch0039.cell0313, Batch0039.tau0313, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3120 | hy3120
    · have hs31201 : InSquare (19/80) (9/80) (1/80) tau := by
        convert childLR hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0312.sound htau (by
        simp only [Batch0039.cell0312, Batch0039.tau0312, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31201 (by positivity) using 1 <;> norm_num)
    · have hs31203 : InSquare (19/80) (11/80) (1/80) tau := by
        convert childUR hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0314.sound htau (by
        simp only [Batch0039.cell0314, Batch0039.tau0314, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3121 | hx3121
  · rcases le_total tau.im (1/8 : ℝ) with hy3121 | hy3121
    · have hs31210 : InSquare (21/80) (9/80) (1/80) tau := by
        convert childLL hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0315.sound htau (by
        simp only [Batch0039.cell0315, Batch0039.tau0315, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31210 (by positivity) using 1 <;> norm_num)
    · have hs31212 : InSquare (21/80) (11/80) (1/80) tau := by
        convert childUL hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0317.sound htau (by
        simp only [Batch0039.cell0317, Batch0039.tau0317, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3121 | hy3121
    · have hs31211 : InSquare (23/80) (9/80) (1/80) tau := by
        convert childLR hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0316.sound htau (by
        simp only [Batch0039.cell0316, Batch0039.tau0316, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31211 (by positivity) using 1 <;> norm_num)
    · have hs31213 : InSquare (23/80) (11/80) (1/80) tau := by
        convert childUR hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0318.sound htau (by
        simp only [Batch0039.cell0318, Batch0039.tau0318, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3122 | hx3122
  · rcases le_total tau.im (7/40 : ℝ) with hy3122 | hy3122
    · have hs31220 : InSquare (17/80) (13/80) (1/80) tau := by
        convert childLL hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0039.cell0319.sound htau (by
        simp only [Batch0039.cell0319, Batch0039.tau0319, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31220 (by positivity) using 1 <;> norm_num)
    · have hs31222 : InSquare (17/80) (3/16) (1/80) tau := by
        convert childUL hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0040.cell0321.sound htau (by
        simp only [Batch0040.cell0321, Batch0040.tau0321, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3122 | hy3122
    · have hs31221 : InSquare (19/80) (13/80) (1/80) tau := by
        convert childLR hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0040.cell0320.sound htau (by
        simp only [Batch0040.cell0320, Batch0040.tau0320, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31221 (by positivity) using 1 <;> norm_num)
    · have hs31223 : InSquare (19/80) (3/16) (1/80) tau := by
        convert childUR hs hx3122 hy3122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx31223 | hx31223
      · rcases le_total tau.im (3/16 : ℝ) with hy31223 | hy31223
        · have hs312230 : InSquare (37/160) (29/160) (1/160) tau := by
            convert childLL hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1002.sound htau (by
            simp only [Batch0125.cell1002, Batch0125.tau1002, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312230 (by positivity) using 1 <;> norm_num)
        · have hs312232 : InSquare (37/160) (31/160) (1/160) tau := by
            convert childUL hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1004.sound htau (by
            simp only [Batch0125.cell1004, Batch0125.tau1004, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31223 | hy31223
        · have hs312231 : InSquare (39/160) (29/160) (1/160) tau := by
            convert childLR hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1003.sound htau (by
            simp only [Batch0125.cell1003, Batch0125.tau1003, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312231 (by positivity) using 1 <;> norm_num)
        · have hs312233 : InSquare (39/160) (31/160) (1/160) tau := by
            convert childUR hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1005.sound htau (by
            simp only [Batch0125.cell1005, Batch0125.tau1005, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3123 | hx3123
  · rcases le_total tau.im (7/40 : ℝ) with hy3123 | hy3123
    · have hs31230 : InSquare (21/80) (13/80) (1/80) tau := by
        convert childLL hs hx3123 hy3123 using 1 <;> norm_num
      exact Batch0040.cell0322.sound htau (by
        simp only [Batch0040.cell0322, Batch0040.tau0322, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31230 (by positivity) using 1 <;> norm_num)
    · have hs31232 : InSquare (21/80) (3/16) (1/80) tau := by
        convert childUL hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx31232 | hx31232
      · rcases le_total tau.im (3/16 : ℝ) with hy31232 | hy31232
        · have hs312320 : InSquare (41/160) (29/160) (1/160) tau := by
            convert childLL hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1010.sound htau (by
            simp only [Batch0126.cell1010, Batch0126.tau1010, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312320 (by positivity) using 1 <;> norm_num)
        · have hs312322 : InSquare (41/160) (31/160) (1/160) tau := by
            convert childUL hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1012.sound htau (by
            simp only [Batch0126.cell1012, Batch0126.tau1012, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31232 | hy31232
        · have hs312321 : InSquare (43/160) (29/160) (1/160) tau := by
            convert childLR hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1011.sound htau (by
            simp only [Batch0126.cell1011, Batch0126.tau1011, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312321 (by positivity) using 1 <;> norm_num)
        · have hs312323 : InSquare (43/160) (31/160) (1/160) tau := by
            convert childUR hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1013.sound htau (by
            simp only [Batch0126.cell1013, Batch0126.tau1013, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3123 | hy3123
    · have hs31231 : InSquare (23/80) (13/80) (1/80) tau := by
        convert childLR hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx31231 | hx31231
      · rcases le_total tau.im (13/80 : ℝ) with hy31231 | hy31231
        · have hs312310 : InSquare (9/32) (5/32) (1/160) tau := by
            convert childLL hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0125.cell1006.sound htau (by
            simp only [Batch0125.cell1006, Batch0125.tau1006, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312310 (by positivity) using 1 <;> norm_num)
        · have hs312312 : InSquare (9/32) (27/160) (1/160) tau := by
            convert childUL hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0126.cell1008.sound htau (by
            simp only [Batch0126.cell1008, Batch0126.tau1008, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31231 | hy31231
        · have hs312311 : InSquare (47/160) (5/32) (1/160) tau := by
            convert childLR hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0125.cell1007.sound htau (by
            simp only [Batch0125.cell1007, Batch0125.tau1007, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312311 (by positivity) using 1 <;> norm_num)
        · have hs312313 : InSquare (47/160) (27/160) (1/160) tau := by
            convert childUR hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0126.cell1009.sound htau (by
            simp only [Batch0126.cell1009, Batch0126.tau1009, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312313 (by positivity) using 1 <;> norm_num)
    · have hs31233 : InSquare (23/80) (3/16) (1/80) tau := by
        convert childUR hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx31233 | hx31233
      · rcases le_total tau.im (3/16 : ℝ) with hy31233 | hy31233
        · have hs312330 : InSquare (9/32) (29/160) (1/160) tau := by
            convert childLL hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0126.cell1014.sound htau (by
            simp only [Batch0126.cell1014, Batch0126.tau1014, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312330 (by positivity) using 1 <;> norm_num)
        · have hs312332 : InSquare (9/32) (31/160) (1/160) tau := by
            convert childUL hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0127.cell1016.sound htau (by
            simp only [Batch0127.cell1016, Batch0127.tau1016, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31233 | hy31233
        · have hs312331 : InSquare (47/160) (29/160) (1/160) tau := by
            convert childLR hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0126.cell1015.sound htau (by
            simp only [Batch0126.cell1015, Batch0126.tau1015, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312331 (by positivity) using 1 <;> norm_num)
        · have hs312333 : InSquare (47/160) (31/160) (1/160) tau := by
            convert childUR hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0127.cell1017.sound htau (by
            simp only [Batch0127.cell1017, Batch0127.tau1017, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3130 | hx3130
  · rcases le_total tau.im (1/8 : ℝ) with hy3130 | hy3130
    · have hs31300 : InSquare (5/16) (9/80) (1/80) tau := by
        convert childLL hs hx3130 hy3130 using 1 <;> norm_num
      exact Batch0040.cell0323.sound htau (by
        simp only [Batch0040.cell0323, Batch0040.tau0323, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31300 (by positivity) using 1 <;> norm_num)
    · have hs31302 : InSquare (5/16) (11/80) (1/80) tau := by
        convert childUL hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31302 | hx31302
      · rcases le_total tau.im (11/80 : ℝ) with hy31302 | hy31302
        · have hs313020 : InSquare (49/160) (21/160) (1/160) tau := by
            convert childLL hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0127.cell1022.sound htau (by
            simp only [Batch0127.cell1022, Batch0127.tau1022, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313020 (by positivity) using 1 <;> norm_num)
        · have hs313022 : InSquare (49/160) (23/160) (1/160) tau := by
            convert childUL hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0128.cell1024.sound htau (by
            simp only [Batch0128.cell1024, Batch0128.tau1024, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31302 | hy31302
        · have hs313021 : InSquare (51/160) (21/160) (1/160) tau := by
            convert childLR hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0127.cell1023.sound htau (by
            simp only [Batch0127.cell1023, Batch0127.tau1023, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313021 (by positivity) using 1 <;> norm_num)
        · have hs313023 : InSquare (51/160) (23/160) (1/160) tau := by
            convert childUR hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0128.cell1025.sound htau (by
            simp only [Batch0128.cell1025, Batch0128.tau1025, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3130 | hy3130
    · have hs31301 : InSquare (27/80) (9/80) (1/80) tau := by
        convert childLR hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31301 | hx31301
      · rcases le_total tau.im (9/80 : ℝ) with hy31301 | hy31301
        · have hs313010 : InSquare (53/160) (17/160) (1/160) tau := by
            convert childLL hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1018.sound htau (by
            simp only [Batch0127.cell1018, Batch0127.tau1018, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313010 (by positivity) using 1 <;> norm_num)
        · have hs313012 : InSquare (53/160) (19/160) (1/160) tau := by
            convert childUL hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1020.sound htau (by
            simp only [Batch0127.cell1020, Batch0127.tau1020, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31301 | hy31301
        · have hs313011 : InSquare (11/32) (17/160) (1/160) tau := by
            convert childLR hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1019.sound htau (by
            simp only [Batch0127.cell1019, Batch0127.tau1019, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313011 (by positivity) using 1 <;> norm_num)
        · have hs313013 : InSquare (11/32) (19/160) (1/160) tau := by
            convert childUR hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1021.sound htau (by
            simp only [Batch0127.cell1021, Batch0127.tau1021, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313013 (by positivity) using 1 <;> norm_num)
    · have hs31303 : InSquare (27/80) (11/80) (1/80) tau := by
        convert childUR hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31303 | hx31303
      · rcases le_total tau.im (11/80 : ℝ) with hy31303 | hy31303
        · have hs313030 : InSquare (53/160) (21/160) (1/160) tau := by
            convert childLL hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1026.sound htau (by
            simp only [Batch0128.cell1026, Batch0128.tau1026, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313030 (by positivity) using 1 <;> norm_num)
        · have hs313032 : InSquare (53/160) (23/160) (1/160) tau := by
            convert childUL hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1028.sound htau (by
            simp only [Batch0128.cell1028, Batch0128.tau1028, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31303 | hy31303
        · have hs313031 : InSquare (11/32) (21/160) (1/160) tau := by
            convert childLR hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1027.sound htau (by
            simp only [Batch0128.cell1027, Batch0128.tau1027, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313031 (by positivity) using 1 <;> norm_num)
        · have hs313033 : InSquare (11/32) (23/160) (1/160) tau := by
            convert childUR hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1029.sound htau (by
            simp only [Batch0128.cell1029, Batch0128.tau1029, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_313111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3131 | hx3131
  · rcases le_total tau.im (1/8 : ℝ) with hy3131 | hy3131
    · have hs31310 : InSquare (29/80) (9/80) (1/80) tau := by
        convert childLL hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31310 | hx31310
      · rcases le_total tau.im (9/80 : ℝ) with hy31310 | hy31310
        · have hs313100 : InSquare (57/160) (17/160) (1/160) tau := by
            convert childLL hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0128.cell1030.sound htau (by
            simp only [Batch0128.cell1030, Batch0128.tau1030, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313100 (by positivity) using 1 <;> norm_num)
        · have hs313102 : InSquare (57/160) (19/160) (1/160) tau := by
            convert childUL hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0129.cell1032.sound htau (by
            simp only [Batch0129.cell1032, Batch0129.tau1032, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31310 | hy31310
        · have hs313101 : InSquare (59/160) (17/160) (1/160) tau := by
            convert childLR hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0128.cell1031.sound htau (by
            simp only [Batch0128.cell1031, Batch0128.tau1031, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313101 (by positivity) using 1 <;> norm_num)
        · have hs313103 : InSquare (59/160) (19/160) (1/160) tau := by
            convert childUR hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0129.cell1033.sound htau (by
            simp only [Batch0129.cell1033, Batch0129.tau1033, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313103 (by positivity) using 1 <;> norm_num)
    · have hs31312 : InSquare (29/80) (11/80) (1/80) tau := by
        convert childUL hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31312 | hx31312
      · rcases le_total tau.im (11/80 : ℝ) with hy31312 | hy31312
        · have hs313120 : InSquare (57/160) (21/160) (1/160) tau := by
            convert childLL hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1036.sound htau (by
            simp only [Batch0129.cell1036, Batch0129.tau1036, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313120 (by positivity) using 1 <;> norm_num)
        · have hs313122 : InSquare (57/160) (23/160) (1/160) tau := by
            convert childUL hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1038.sound htau (by
            simp only [Batch0129.cell1038, Batch0129.tau1038, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31312 | hy31312
        · have hs313121 : InSquare (59/160) (21/160) (1/160) tau := by
            convert childLR hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1037.sound htau (by
            simp only [Batch0129.cell1037, Batch0129.tau1037, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313121 (by positivity) using 1 <;> norm_num)
        · have hs313123 : InSquare (59/160) (23/160) (1/160) tau := by
            convert childUR hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1039.sound htau (by
            simp only [Batch0129.cell1039, Batch0129.tau1039, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3131 | hy3131
    · have hs31311 : InSquare (31/80) (9/80) (1/80) tau := by
        convert childLR hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31311 | hx31311
      · rcases le_total tau.im (9/80 : ℝ) with hy31311 | hy31311
        · have hs313110 : InSquare (61/160) (17/160) (1/160) tau := by
            convert childLL hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact Batch0129.cell1034.sound htau (by
            simp only [Batch0129.cell1034, Batch0129.tau1034, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313110 (by positivity) using 1 <;> norm_num)
        · have hs313112 : InSquare (61/160) (19/160) (1/160) tau := by
            convert childUL hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact Batch0129.cell1035.sound htau (by
            simp only [Batch0129.cell1035, Batch0129.tau1035, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31311 | hy31311
        · have hs313111 : InSquare (63/160) (17/160) (1/160) tau := by
            convert childLR hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact (outside_313111 htau hs313111).elim
        · have hs313113 : InSquare (63/160) (19/160) (1/160) tau := by
            convert childUR hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact (outside_313113 htau hs313113).elim
    · have hs31313 : InSquare (31/80) (11/80) (1/80) tau := by
        convert childUR hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31313 | hx31313
      · rcases le_total tau.im (11/80 : ℝ) with hy31313 | hy31313
        · have hs313130 : InSquare (61/160) (21/160) (1/160) tau := by
            convert childLL hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact Batch0130.cell1040.sound htau (by
            simp only [Batch0130.cell1040, Batch0130.tau1040, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313130 (by positivity) using 1 <;> norm_num)
        · have hs313132 : InSquare (61/160) (23/160) (1/160) tau := by
            convert childUL hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact Batch0130.cell1041.sound htau (by
            simp only [Batch0130.cell1041, Batch0130.tau1041, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31313 | hy31313
        · have hs313131 : InSquare (63/160) (21/160) (1/160) tau := by
            convert childLR hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact (outside_313131 htau hs313131).elim
        · have hs313133 : InSquare (63/160) (23/160) (1/160) tau := by
            convert childUR hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact (outside_313133 htau hs313133).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131

end


