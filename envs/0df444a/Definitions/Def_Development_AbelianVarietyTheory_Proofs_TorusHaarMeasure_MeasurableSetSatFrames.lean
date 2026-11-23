-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:16.305321+00:00
-- url     : https://prove2.me/theorems/df1adaf2-dd67-412a-bf82-fb803e09193f
-- title:
--   Measurable Set Sat Frames
-- statement:
--   Definitions and structural lemmas for Measurable Set Sat Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
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
namespace GlobalTheory.Unfold
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def satFrames (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ z ∈ A, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b}
end GlobalTheory.Unfold


