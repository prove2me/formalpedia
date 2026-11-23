-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:29.568245+00:00
-- url     : https://prove2.me/theorems/4985ffb3-9ab5-4f4a-945b-9589d02402b4
-- title:
--   Index Range Mul Vec Lin Eq Abs Norm Det
-- statement:
--   Definitions and structural lemmas for Index Range Mul Vec Lin Eq Abs Norm Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IndexRangeMulVecLinEqAbsNormDet.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
end GlobalTheory


