-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:33.193413+00:00
-- url     : https://prove2.me/theorems/84c6e473-3519-4dd2-8be7-73097ce1787c
-- title:
--   Measurable Set Bor Sat
-- statement:
--   Definitions and structural lemmas for Measurable Set Bor Sat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
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
namespace GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}
end GlobalTheory.FrameMeas


