-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetDivIndexEqOfSpanEq
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetDivIndexEqOfSpanEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:59.21319+00:00
-- url     : https://prove2.me/theorems/c46e6cda-3d9d-4b3a-a0b1-f0efa7e7fed7
-- title:
--   Gram Det Div Index Eq Of Span Eq
-- statement:
--   Definitions and structural lemmas for Gram Det Div Index Eq Of Span Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetDivIndexEqOfSpanEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory


