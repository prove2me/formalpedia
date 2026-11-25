-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:53.01612+00:00
-- url     : https://prove2.me/theorems/0e0ae882-2347-4b59-9a43-f3e8ef23b470
-- title:
--   Of Real Rpow Neg Le
-- statement:
--   Definitions and structural lemmas for Of Real Rpow Neg Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealRpowNegLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.Up.DivMetricPf
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)
end GlobalTheory.Up.DivMetricPf


