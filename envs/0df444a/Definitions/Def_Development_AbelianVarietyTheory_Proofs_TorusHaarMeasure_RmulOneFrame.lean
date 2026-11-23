-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:00.291043+00:00
-- url     : https://prove2.me/theorems/3ac12be6-bb5e-4ba6-b7c2-3381298f6f0e
-- title:
--   Rmul One Frame
-- statement:
--   Definitions and structural lemmas for Rmul One Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RmulOneFrame.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.ProperDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
end GlobalTheory.ProperDiscontinuity


