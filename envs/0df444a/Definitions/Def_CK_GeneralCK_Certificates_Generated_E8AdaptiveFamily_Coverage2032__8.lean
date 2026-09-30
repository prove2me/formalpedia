-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2032__8
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2032__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:11:55.342762+00:00
-- url     : https://prove2.me/theorems/5dd2b13e-f673-432a-af9c-b12fbead1b1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032 (+7 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2032 (+7 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2033, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2120, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2122, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2123, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2132, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2201, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2203).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0106
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0031
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0237
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2032 | hx2032
  · rcases le_total tau.im (7/40 : ℝ) with hy2032 | hy2032
    · have hs20320 : InSquare (-23/80) (13/80) (1/80) tau := by
        convert childLL hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx20320 | hx20320
      · rcases le_total tau.im (13/80 : ℝ) with hy20320 | hy20320
        · have hs203200 : InSquare (-47/160) (5/32) (1/160) tau := by
            convert childLL hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0833.sound htau (by
            simp only [Batch0104.cell0833, Batch0104.tau0833, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203200 (by positivity) using 1 <;> norm_num)
        · have hs203202 : InSquare (-47/160) (27/160) (1/160) tau := by
            convert childUL hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0835.sound htau (by
            simp only [Batch0104.cell0835, Batch0104.tau0835, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20320 | hy20320
        · have hs203201 : InSquare (-9/32) (5/32) (1/160) tau := by
            convert childLR hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0834.sound htau (by
            simp only [Batch0104.cell0834, Batch0104.tau0834, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203201 (by positivity) using 1 <;> norm_num)
        · have hs203203 : InSquare (-9/32) (27/160) (1/160) tau := by
            convert childUR hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0836.sound htau (by
            simp only [Batch0104.cell0836, Batch0104.tau0836, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203203 (by positivity) using 1 <;> norm_num)
    · have hs20322 : InSquare (-23/80) (3/16) (1/80) tau := by
        convert childUL hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx20322 | hx20322
      · rcases le_total tau.im (3/16 : ℝ) with hy20322 | hy20322
        · have hs203220 : InSquare (-47/160) (29/160) (1/160) tau := by
            convert childLL hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0837.sound htau (by
            simp only [Batch0104.cell0837, Batch0104.tau0837, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203220 (by positivity) using 1 <;> norm_num)
        · have hs203222 : InSquare (-47/160) (31/160) (1/160) tau := by
            convert childUL hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0839.sound htau (by
            simp only [Batch0104.cell0839, Batch0104.tau0839, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20322 | hy20322
        · have hs203221 : InSquare (-9/32) (29/160) (1/160) tau := by
            convert childLR hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0838.sound htau (by
            simp only [Batch0104.cell0838, Batch0104.tau0838, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203221 (by positivity) using 1 <;> norm_num)
        · have hs203223 : InSquare (-9/32) (31/160) (1/160) tau := by
            convert childUR hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0105.cell0840.sound htau (by
            simp only [Batch0105.cell0840, Batch0105.tau0840, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2032 | hy2032
    · have hs20321 : InSquare (-21/80) (13/80) (1/80) tau := by
        convert childLR hs hx2032 hy2032 using 1 <;> norm_num
      exact Batch0028.cell0231.sound htau (by
        simp only [Batch0028.cell0231, Batch0028.tau0231, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20321 (by positivity) using 1 <;> norm_num)
    · have hs20323 : InSquare (-21/80) (3/16) (1/80) tau := by
        convert childUR hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx20323 | hx20323
      · rcases le_total tau.im (3/16 : ℝ) with hy20323 | hy20323
        · have hs203230 : InSquare (-43/160) (29/160) (1/160) tau := by
            convert childLL hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0841.sound htau (by
            simp only [Batch0105.cell0841, Batch0105.tau0841, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203230 (by positivity) using 1 <;> norm_num)
        · have hs203232 : InSquare (-43/160) (31/160) (1/160) tau := by
            convert childUL hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0843.sound htau (by
            simp only [Batch0105.cell0843, Batch0105.tau0843, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20323 | hy20323
        · have hs203231 : InSquare (-41/160) (29/160) (1/160) tau := by
            convert childLR hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0842.sound htau (by
            simp only [Batch0105.cell0842, Batch0105.tau0842, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203231 (by positivity) using 1 <;> norm_num)
        · have hs203233 : InSquare (-41/160) (31/160) (1/160) tau := by
            convert childUR hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0844.sound htau (by
            simp only [Batch0105.cell0844, Batch0105.tau0844, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2033 | hx2033
  · rcases le_total tau.im (7/40 : ℝ) with hy2033 | hy2033
    · have hs20330 : InSquare (-19/80) (13/80) (1/80) tau := by
        convert childLL hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0232.sound htau (by
        simp only [Batch0029.cell0232, Batch0029.tau0232, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20330 (by positivity) using 1 <;> norm_num)
    · have hs20332 : InSquare (-19/80) (3/16) (1/80) tau := by
        convert childUL hs hx2033 hy2033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx20332 | hx20332
      · rcases le_total tau.im (3/16 : ℝ) with hy20332 | hy20332
        · have hs203320 : InSquare (-39/160) (29/160) (1/160) tau := by
            convert childLL hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0845.sound htau (by
            simp only [Batch0105.cell0845, Batch0105.tau0845, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203320 (by positivity) using 1 <;> norm_num)
        · have hs203322 : InSquare (-39/160) (31/160) (1/160) tau := by
            convert childUL hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0847.sound htau (by
            simp only [Batch0105.cell0847, Batch0105.tau0847, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20332 | hy20332
        · have hs203321 : InSquare (-37/160) (29/160) (1/160) tau := by
            convert childLR hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0846.sound htau (by
            simp only [Batch0105.cell0846, Batch0105.tau0846, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203321 (by positivity) using 1 <;> norm_num)
        · have hs203323 : InSquare (-37/160) (31/160) (1/160) tau := by
            convert childUR hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0106.cell0848.sound htau (by
            simp only [Batch0106.cell0848, Batch0106.tau0848, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2033 | hy2033
    · have hs20331 : InSquare (-17/80) (13/80) (1/80) tau := by
        convert childLR hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0233.sound htau (by
        simp only [Batch0029.cell0233, Batch0029.tau0233, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20331 (by positivity) using 1 <;> norm_num)
    · have hs20333 : InSquare (-17/80) (3/16) (1/80) tau := by
        convert childUR hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0234.sound htau (by
        simp only [Batch0029.cell0234, Batch0029.tau0234, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2120 | hx2120
  · rcases le_total tau.im (1/8 : ℝ) with hy2120 | hy2120
    · have hs21200 : InSquare (-3/16) (9/80) (1/80) tau := by
        convert childLL hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0235.sound htau (by
        simp only [Batch0029.cell0235, Batch0029.tau0235, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21200 (by positivity) using 1 <;> norm_num)
    · have hs21202 : InSquare (-3/16) (11/80) (1/80) tau := by
        convert childUL hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0237.sound htau (by
        simp only [Batch0029.cell0237, Batch0029.tau0237, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2120 | hy2120
    · have hs21201 : InSquare (-13/80) (9/80) (1/80) tau := by
        convert childLR hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0236.sound htau (by
        simp only [Batch0029.cell0236, Batch0029.tau0236, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21201 (by positivity) using 1 <;> norm_num)
    · have hs21203 : InSquare (-13/80) (11/80) (1/80) tau := by
        convert childUR hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0238.sound htau (by
        simp only [Batch0029.cell0238, Batch0029.tau0238, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2122 | hx2122
  · rcases le_total tau.im (7/40 : ℝ) with hy2122 | hy2122
    · have hs21220 : InSquare (-3/16) (13/80) (1/80) tau := by
        convert childLL hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0029.cell0239.sound htau (by
        simp only [Batch0029.cell0239, Batch0029.tau0239, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21220 (by positivity) using 1 <;> norm_num)
    · have hs21222 : InSquare (-3/16) (3/16) (1/80) tau := by
        convert childUL hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0241.sound htau (by
        simp only [Batch0030.cell0241, Batch0030.tau0241, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2122 | hy2122
    · have hs21221 : InSquare (-13/80) (13/80) (1/80) tau := by
        convert childLR hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0240.sound htau (by
        simp only [Batch0030.cell0240, Batch0030.tau0240, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21221 (by positivity) using 1 <;> norm_num)
    · have hs21223 : InSquare (-13/80) (3/16) (1/80) tau := by
        convert childUR hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0242.sound htau (by
        simp only [Batch0030.cell0242, Batch0030.tau0242, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2123 | hx2123
  · rcases le_total tau.im (7/40 : ℝ) with hy2123 | hy2123
    · have hs21230 : InSquare (-11/80) (13/80) (1/80) tau := by
        convert childLL hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0243.sound htau (by
        simp only [Batch0030.cell0243, Batch0030.tau0243, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21230 (by positivity) using 1 <;> norm_num)
    · have hs21232 : InSquare (-11/80) (3/16) (1/80) tau := by
        convert childUL hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0245.sound htau (by
        simp only [Batch0030.cell0245, Batch0030.tau0245, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2123 | hy2123
    · have hs21231 : InSquare (-9/80) (13/80) (1/80) tau := by
        convert childLR hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0244.sound htau (by
        simp only [Batch0030.cell0244, Batch0030.tau0244, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21231 (by positivity) using 1 <;> norm_num)
    · have hs21233 : InSquare (-9/80) (3/16) (1/80) tau := by
        convert childUR hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0246.sound htau (by
        simp only [Batch0030.cell0246, Batch0030.tau0246, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2132 | hx2132
  · rcases le_total tau.im (7/40 : ℝ) with hy2132 | hy2132
    · have hs21320 : InSquare (-7/80) (13/80) (1/80) tau := by
        convert childLL hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0030.cell0247.sound htau (by
        simp only [Batch0030.cell0247, Batch0030.tau0247, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21320 (by positivity) using 1 <;> norm_num)
    · have hs21322 : InSquare (-7/80) (3/16) (1/80) tau := by
        convert childUL hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0249.sound htau (by
        simp only [Batch0031.cell0249, Batch0031.tau0249, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2132 | hy2132
    · have hs21321 : InSquare (-1/16) (13/80) (1/80) tau := by
        convert childLR hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0248.sound htau (by
        simp only [Batch0031.cell0248, Batch0031.tau0248, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21321 (by positivity) using 1 <;> norm_num)
    · have hs21323 : InSquare (-1/16) (3/16) (1/80) tau := by
        convert childUR hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0250.sound htau (by
        simp only [Batch0031.cell0250, Batch0031.tau0250, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_220120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/160) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-103/320) (79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2201 | hx2201
  · rcases le_total tau.im (9/40 : ℝ) with hy2201 | hy2201
    · have hs22010 : InSquare (-27/80) (17/80) (1/80) tau := by
        convert childLL hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx22010 | hx22010
      · rcases le_total tau.im (17/80 : ℝ) with hy22010 | hy22010
        · have hs220100 : InSquare (-11/32) (33/160) (1/160) tau := by
            convert childLL hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx220100 | hx220100
          · rcases le_total tau.im (33/160 : ℝ) with hy220100 | hy220100
            · have hs2201000 : InSquare (-111/320) (13/64) (1/320) tau := by
                convert childLL hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1883.sound htau (by
                simp only [Batch0235.cell1883, Batch0235.tau1883, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201000 (by positivity) using 1 <;> norm_num)
            · have hs2201002 : InSquare (-111/320) (67/320) (1/320) tau := by
                convert childUL hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact (outside_2201002 htau hs2201002).elim
          · rcases le_total tau.im (33/160 : ℝ) with hy220100 | hy220100
            · have hs2201001 : InSquare (-109/320) (13/64) (1/320) tau := by
                convert childLR hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1884.sound htau (by
                simp only [Batch0235.cell1884, Batch0235.tau1884, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201001 (by positivity) using 1 <;> norm_num)
            · have hs2201003 : InSquare (-109/320) (67/320) (1/320) tau := by
                convert childUR hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1885.sound htau (by
                simp only [Batch0235.cell1885, Batch0235.tau1885, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201003 (by positivity) using 1 <;> norm_num)
        · have hs220102 : InSquare (-11/32) (7/32) (1/160) tau := by
            convert childUL hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx220102 | hx220102
          · rcases le_total tau.im (7/32 : ℝ) with hy220102 | hy220102
            · have hs2201020 : InSquare (-111/320) (69/320) (1/320) tau := by
                convert childLL hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201020 htau hs2201020).elim
            · have hs2201022 : InSquare (-111/320) (71/320) (1/320) tau := by
                convert childUL hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201022 htau hs2201022).elim
          · rcases le_total tau.im (7/32 : ℝ) with hy220102 | hy220102
            · have hs2201021 : InSquare (-109/320) (69/320) (1/320) tau := by
                convert childLR hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact Batch0235.cell1886.sound htau (by
                simp only [Batch0235.cell1886, Batch0235.tau1886, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201021 (by positivity) using 1 <;> norm_num)
            · have hs2201023 : InSquare (-109/320) (71/320) (1/320) tau := by
                convert childUR hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201023 htau hs2201023).elim
      · rcases le_total tau.im (17/80 : ℝ) with hy22010 | hy22010
        · have hs220101 : InSquare (-53/160) (33/160) (1/160) tau := by
            convert childLR hs22010 hx22010 hy22010 using 1 <;> norm_num
          exact Batch0106.cell0849.sound htau (by
            simp only [Batch0106.cell0849, Batch0106.tau0849, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220101 (by positivity) using 1 <;> norm_num)
        · have hs220103 : InSquare (-53/160) (7/32) (1/160) tau := by
            convert childUR hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx220103 | hx220103
          · rcases le_total tau.im (7/32 : ℝ) with hy220103 | hy220103
            · have hs2201030 : InSquare (-107/320) (69/320) (1/320) tau := by
                convert childLL hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0235.cell1887.sound htau (by
                simp only [Batch0235.cell1887, Batch0235.tau1887, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201030 (by positivity) using 1 <;> norm_num)
            · have hs2201032 : InSquare (-107/320) (71/320) (1/320) tau := by
                convert childUL hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1889.sound htau (by
                simp only [Batch0236.cell1889, Batch0236.tau1889, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (7/32 : ℝ) with hy220103 | hy220103
            · have hs2201031 : InSquare (-21/64) (69/320) (1/320) tau := by
                convert childLR hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1888.sound htau (by
                simp only [Batch0236.cell1888, Batch0236.tau1888, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201031 (by positivity) using 1 <;> norm_num)
            · have hs2201033 : InSquare (-21/64) (71/320) (1/320) tau := by
                convert childUR hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1890.sound htau (by
                simp only [Batch0236.cell1890, Batch0236.tau1890, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201033 (by positivity) using 1 <;> norm_num)
    · have hs22012 : InSquare (-27/80) (19/80) (1/80) tau := by
        convert childUL hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx22012 | hx22012
      · rcases le_total tau.im (19/80 : ℝ) with hy22012 | hy22012
        · have hs220120 : InSquare (-11/32) (37/160) (1/160) tau := by
            convert childLL hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220120 htau hs220120).elim
        · have hs220122 : InSquare (-11/32) (39/160) (1/160) tau := by
            convert childUL hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220122 htau hs220122).elim
      · rcases le_total tau.im (19/80 : ℝ) with hy22012 | hy22012
        · have hs220121 : InSquare (-53/160) (37/160) (1/160) tau := by
            convert childLR hs22012 hx22012 hy22012 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx220121 | hx220121
          · rcases le_total tau.im (37/160 : ℝ) with hy220121 | hy220121
            · have hs2201210 : InSquare (-107/320) (73/320) (1/320) tau := by
                convert childLL hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact (outside_2201210 htau hs2201210).elim
            · have hs2201212 : InSquare (-107/320) (15/64) (1/320) tau := by
                convert childUL hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact (outside_2201212 htau hs2201212).elim
          · rcases le_total tau.im (37/160 : ℝ) with hy220121 | hy220121
            · have hs2201211 : InSquare (-21/64) (73/320) (1/320) tau := by
                convert childLR hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact Batch0236.cell1891.sound htau (by
                simp only [Batch0236.cell1891, Batch0236.tau1891, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201211 (by positivity) using 1 <;> norm_num)
            · have hs2201213 : InSquare (-21/64) (15/64) (1/320) tau := by
                convert childUR hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact Batch0236.cell1892.sound htau (by
                simp only [Batch0236.cell1892, Batch0236.tau1892, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201213 (by positivity) using 1 <;> norm_num)
        · have hs220123 : InSquare (-53/160) (39/160) (1/160) tau := by
            convert childUR hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220123 htau hs220123).elim
  · rcases le_total tau.im (9/40 : ℝ) with hy2201 | hy2201
    · have hs22011 : InSquare (-5/16) (17/80) (1/80) tau := by
        convert childLR hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22011 | hx22011
      · rcases le_total tau.im (17/80 : ℝ) with hy22011 | hy22011
        · have hs220110 : InSquare (-51/160) (33/160) (1/160) tau := by
            convert childLL hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0850.sound htau (by
            simp only [Batch0106.cell0850, Batch0106.tau0850, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220110 (by positivity) using 1 <;> norm_num)
        · have hs220112 : InSquare (-51/160) (7/32) (1/160) tau := by
            convert childUL hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0852.sound htau (by
            simp only [Batch0106.cell0852, Batch0106.tau0852, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22011 | hy22011
        · have hs220111 : InSquare (-49/160) (33/160) (1/160) tau := by
            convert childLR hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0851.sound htau (by
            simp only [Batch0106.cell0851, Batch0106.tau0851, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220111 (by positivity) using 1 <;> norm_num)
        · have hs220113 : InSquare (-49/160) (7/32) (1/160) tau := by
            convert childUR hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0853.sound htau (by
            simp only [Batch0106.cell0853, Batch0106.tau0853, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220113 (by positivity) using 1 <;> norm_num)
    · have hs22013 : InSquare (-5/16) (19/80) (1/80) tau := by
        convert childUR hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22013 | hx22013
      · rcases le_total tau.im (19/80 : ℝ) with hy22013 | hy22013
        · have hs220130 : InSquare (-51/160) (37/160) (1/160) tau := by
            convert childLL hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx220130 | hx220130
          · rcases le_total tau.im (37/160 : ℝ) with hy220130 | hy220130
            · have hs2201300 : InSquare (-103/320) (73/320) (1/320) tau := by
                convert childLL hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1893.sound htau (by
                simp only [Batch0236.cell1893, Batch0236.tau1893, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201300 (by positivity) using 1 <;> norm_num)
            · have hs2201302 : InSquare (-103/320) (15/64) (1/320) tau := by
                convert childUL hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1895.sound htau (by
                simp only [Batch0236.cell1895, Batch0236.tau1895, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy220130 | hy220130
            · have hs2201301 : InSquare (-101/320) (73/320) (1/320) tau := by
                convert childLR hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1894.sound htau (by
                simp only [Batch0236.cell1894, Batch0236.tau1894, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201301 (by positivity) using 1 <;> norm_num)
            · have hs2201303 : InSquare (-101/320) (15/64) (1/320) tau := by
                convert childUR hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0237.cell1896.sound htau (by
                simp only [Batch0237.cell1896, Batch0237.tau1896, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201303 (by positivity) using 1 <;> norm_num)
        · have hs220132 : InSquare (-51/160) (39/160) (1/160) tau := by
            convert childUL hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx220132 | hx220132
          · rcases le_total tau.im (39/160 : ℝ) with hy220132 | hy220132
            · have hs2201320 : InSquare (-103/320) (77/320) (1/320) tau := by
                convert childLL hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1897.sound htau (by
                simp only [Batch0237.cell1897, Batch0237.tau1897, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201320 (by positivity) using 1 <;> norm_num)
            · have hs2201322 : InSquare (-103/320) (79/320) (1/320) tau := by
                convert childUL hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact (outside_2201322 htau hs2201322).elim
          · rcases le_total tau.im (39/160 : ℝ) with hy220132 | hy220132
            · have hs2201321 : InSquare (-101/320) (77/320) (1/320) tau := by
                convert childLR hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1898.sound htau (by
                simp only [Batch0237.cell1898, Batch0237.tau1898, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201321 (by positivity) using 1 <;> norm_num)
            · have hs2201323 : InSquare (-101/320) (79/320) (1/320) tau := by
                convert childUR hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1899.sound htau (by
                simp only [Batch0237.cell1899, Batch0237.tau1899, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22013 | hy22013
        · have hs220131 : InSquare (-49/160) (37/160) (1/160) tau := by
            convert childLR hs22013 hx22013 hy22013 using 1 <;> norm_num
          exact Batch0106.cell0854.sound htau (by
            simp only [Batch0106.cell0854, Batch0106.tau0854, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220131 (by positivity) using 1 <;> norm_num)
        · have hs220133 : InSquare (-49/160) (39/160) (1/160) tau := by
            convert childUR hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220133 | hx220133
          · rcases le_total tau.im (39/160 : ℝ) with hy220133 | hy220133
            · have hs2201330 : InSquare (-99/320) (77/320) (1/320) tau := by
                convert childLL hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1900.sound htau (by
                simp only [Batch0237.cell1900, Batch0237.tau1900, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201330 (by positivity) using 1 <;> norm_num)
            · have hs2201332 : InSquare (-99/320) (79/320) (1/320) tau := by
                convert childUL hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1902.sound htau (by
                simp only [Batch0237.cell1902, Batch0237.tau1902, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy220133 | hy220133
            · have hs2201331 : InSquare (-97/320) (77/320) (1/320) tau := by
                convert childLR hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1901.sound htau (by
                simp only [Batch0237.cell1901, Batch0237.tau1901, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201331 (by positivity) using 1 <;> norm_num)
            · have hs2201333 : InSquare (-97/320) (79/320) (1/320) tau := by
                convert childUR hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1903.sound htau (by
                simp only [Batch0237.cell1903, Batch0237.tau1903, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_22030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/16) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2203 | hx2203
  · rcases le_total tau.im (11/40 : ℝ) with hy2203 | hy2203
    · have hs22030 : InSquare (-27/80) (21/80) (1/80) tau := by
        convert childLL hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22030 htau hs22030).elim
    · have hs22032 : InSquare (-27/80) (23/80) (1/80) tau := by
        convert childUL hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22032 htau hs22032).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy2203 | hy2203
    · have hs22031 : InSquare (-5/16) (21/80) (1/80) tau := by
        convert childLR hs hx2203 hy2203 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22031 | hx22031
      · rcases le_total tau.im (21/80 : ℝ) with hy22031 | hy22031
        · have hs220310 : InSquare (-51/160) (41/160) (1/160) tau := by
            convert childLL hs22031 hx22031 hy22031 using 1 <;> norm_num
          exact (outside_220310 htau hs220310).elim
        · have hs220312 : InSquare (-51/160) (43/160) (1/160) tau := by
            convert childUL hs22031 hx22031 hy22031 using 1 <;> norm_num
          exact (outside_220312 htau hs220312).elim
      · rcases le_total tau.im (21/80 : ℝ) with hy22031 | hy22031
        · have hs220311 : InSquare (-49/160) (41/160) (1/160) tau := by
            convert childLR hs22031 hx22031 hy22031 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220311 | hx220311
          · rcases le_total tau.im (41/160 : ℝ) with hy220311 | hy220311
            · have hs2203110 : InSquare (-99/320) (81/320) (1/320) tau := by
                convert childLL hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1904.sound htau (by
                simp only [Batch0238.cell1904, Batch0238.tau1904, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203110 (by positivity) using 1 <;> norm_num)
            · have hs2203112 : InSquare (-99/320) (83/320) (1/320) tau := by
                convert childUL hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1906.sound htau (by
                simp only [Batch0238.cell1906, Batch0238.tau1906, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy220311 | hy220311
            · have hs2203111 : InSquare (-97/320) (81/320) (1/320) tau := by
                convert childLR hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1905.sound htau (by
                simp only [Batch0238.cell1905, Batch0238.tau1905, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203111 (by positivity) using 1 <;> norm_num)
            · have hs2203113 : InSquare (-97/320) (83/320) (1/320) tau := by
                convert childUR hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1907.sound htau (by
                simp only [Batch0238.cell1907, Batch0238.tau1907, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203113 (by positivity) using 1 <;> norm_num)
        · have hs220313 : InSquare (-49/160) (43/160) (1/160) tau := by
            convert childUR hs22031 hx22031 hy22031 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220313 | hx220313
          · rcases le_total tau.im (43/160 : ℝ) with hy220313 | hy220313
            · have hs2203130 : InSquare (-99/320) (17/64) (1/320) tau := by
                convert childLL hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203130 htau hs2203130).elim
            · have hs2203132 : InSquare (-99/320) (87/320) (1/320) tau := by
                convert childUL hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203132 htau hs2203132).elim
          · rcases le_total tau.im (43/160 : ℝ) with hy220313 | hy220313
            · have hs2203131 : InSquare (-97/320) (17/64) (1/320) tau := by
                convert childLR hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact Batch0238.cell1908.sound htau (by
                simp only [Batch0238.cell1908, Batch0238.tau1908, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203131 (by positivity) using 1 <;> norm_num)
            · have hs2203133 : InSquare (-97/320) (87/320) (1/320) tau := by
                convert childUR hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203133 htau hs2203133).elim
    · have hs22033 : InSquare (-5/16) (23/80) (1/80) tau := by
        convert childUR hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22033 htau hs22033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203

end


