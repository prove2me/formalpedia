-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:56.19098+00:00
-- url     : https://prove2.me/theorems/3ddf407a-e3f5-45f5-8462-60b26d0d32ce
-- title:
--   Interp Statement Pf E
-- statement:
--   Definitions and structural lemmas for Interp Statement Pf E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfE.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
def epunct (e : V n → ℝ) (g : V n → ℂ) (y : V n) : ℝ :=
  e y + (Real.log (1 + Complex.normSq (g y)) - Real.log (Complex.normSq (g y)))
variable {U : Set (V n)}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE


