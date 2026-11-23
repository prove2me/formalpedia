-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:34.238601+00:00
-- url     : https://prove2.me/theorems/7af62902-a8fe-4bb3-bf67-537dfc32a0ff
-- title:
--   Phla Block Wt Cpt
-- statement:
--   Definitions and structural lemmas for Phla Block Wt Cpt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PhlaBlockWtCpt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
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
namespace GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def blockWt {r : ℕ} (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then 0 else 1
end GlobalTheory.CurvMargin


