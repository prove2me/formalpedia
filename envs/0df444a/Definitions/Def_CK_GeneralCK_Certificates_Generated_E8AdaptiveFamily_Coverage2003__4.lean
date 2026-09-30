-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2003__4
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Coverage2003__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:11:46.919748+00:00
-- url     : https://prove2.me/theorems/5a55566a-e819-4da8-91ed-a328b107e84c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010, GeneralCK.Certific…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003 (+3 modules: GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012, GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2003 (+3 modules: GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2010, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2012, GeneralCK/Certificates/Generated/E8AdaptiveFamily/Coverage2013).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_CoverageKernel
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0026
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2003 | hx2003
  · rcases le_total tau.im (3/40 : ℝ) with hy2003 | hy2003
    · have hs20030 : InSquare (-27/80) (1/16) (1/80) tau := by
        convert childLL hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0025.cell0206.sound htau (by
        simp only [Batch0025.cell0206, Batch0025.tau0206, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20030 (by positivity) using 1 <;> norm_num)
    · have hs20032 : InSquare (-27/80) (7/80) (1/80) tau := by
        convert childUL hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0026.cell0208.sound htau (by
        simp only [Batch0026.cell0208, Batch0026.tau0208, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2003 | hy2003
    · have hs20031 : InSquare (-5/16) (1/16) (1/80) tau := by
        convert childLR hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0025.cell0207.sound htau (by
        simp only [Batch0025.cell0207, Batch0025.tau0207, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20031 (by positivity) using 1 <;> norm_num)
    · have hs20033 : InSquare (-5/16) (7/80) (1/80) tau := by
        convert childUR hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0026.cell0209.sound htau (by
        simp only [Batch0026.cell0209, Batch0026.tau0209, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2010 | hx2010
  · rcases le_total tau.im (1/40 : ℝ) with hy2010 | hy2010
    · have hs20100 : InSquare (-23/80) (1/80) (1/80) tau := by
        convert childLL hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0210.sound htau (by
        simp only [Batch0026.cell0210, Batch0026.tau0210, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20100 (by positivity) using 1 <;> norm_num)
    · have hs20102 : InSquare (-23/80) (3/80) (1/80) tau := by
        convert childUL hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0212.sound htau (by
        simp only [Batch0026.cell0212, Batch0026.tau0212, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2010 | hy2010
    · have hs20101 : InSquare (-21/80) (1/80) (1/80) tau := by
        convert childLR hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0211.sound htau (by
        simp only [Batch0026.cell0211, Batch0026.tau0211, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20101 (by positivity) using 1 <;> norm_num)
    · have hs20103 : InSquare (-21/80) (3/80) (1/80) tau := by
        convert childUR hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0213.sound htau (by
        simp only [Batch0026.cell0213, Batch0026.tau0213, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2012 | hx2012
  · rcases le_total tau.im (3/40 : ℝ) with hy2012 | hy2012
    · have hs20120 : InSquare (-23/80) (1/16) (1/80) tau := by
        convert childLL hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0026.cell0214.sound htau (by
        simp only [Batch0026.cell0214, Batch0026.tau0214, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20120 (by positivity) using 1 <;> norm_num)
    · have hs20122 : InSquare (-23/80) (7/80) (1/80) tau := by
        convert childUL hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0027.cell0216.sound htau (by
        simp only [Batch0027.cell0216, Batch0027.tau0216, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2012 | hy2012
    · have hs20121 : InSquare (-21/80) (1/16) (1/80) tau := by
        convert childLR hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0026.cell0215.sound htau (by
        simp only [Batch0026.cell0215, Batch0026.tau0215, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20121 (by positivity) using 1 <;> norm_num)
    · have hs20123 : InSquare (-21/80) (7/80) (1/80) tau := by
        convert childUR hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0027.cell0217.sound htau (by
        simp only [Batch0027.cell0217, Batch0027.tau0217, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012

end

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013 =====
section

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2013 | hx2013
  · rcases le_total tau.im (3/40 : ℝ) with hy2013 | hy2013
    · have hs20130 : InSquare (-19/80) (1/16) (1/80) tau := by
        convert childLL hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0218.sound htau (by
        simp only [Batch0027.cell0218, Batch0027.tau0218, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20130 (by positivity) using 1 <;> norm_num)
    · have hs20132 : InSquare (-19/80) (7/80) (1/80) tau := by
        convert childUL hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0220.sound htau (by
        simp only [Batch0027.cell0220, Batch0027.tau0220, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2013 | hy2013
    · have hs20131 : InSquare (-17/80) (1/16) (1/80) tau := by
        convert childLR hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0219.sound htau (by
        simp only [Batch0027.cell0219, Batch0027.tau0219, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20131 (by positivity) using 1 <;> norm_num)
    · have hs20133 : InSquare (-17/80) (7/80) (1/80) tau := by
        convert childUR hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0221.sound htau (by
        simp only [Batch0027.cell0221, Batch0027.tau0221, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013

end


