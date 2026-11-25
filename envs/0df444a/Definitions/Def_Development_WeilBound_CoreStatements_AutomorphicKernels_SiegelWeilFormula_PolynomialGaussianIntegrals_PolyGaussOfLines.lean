-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:00.990703+00:00
-- url     : https://prove2.me/theorems/3b0a4861-682a-4608-b348-16e9c898a398
-- title:
--   Poly Gauss Of Lines
-- statement:
--   Definitions and structural lemmas for Poly Gauss Of Lines, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/PolyGaussOfLines.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory
namespace PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
def gW (c : ℝ) (h : EuclideanSpace ℝ ι → ℂ) (u : EuclideanSpace ℝ ι) : ℂ := h u * (Real.exp (-(c * ‖u‖ ^ 2)) : ℂ)
def Kf (c : ℝ) (h : EuclideanSpace ℝ ι → ℂ) (η : EuclideanSpace ℝ ι) : ℂ :=
  (Real.exp (Real.pi ^ 2 / (2 * c) * ‖η‖ ^ 2) : ℂ) * 𝓕 (gW c h) η
end PositivityTheory.SiegelWeilFormula.KFPB
end


