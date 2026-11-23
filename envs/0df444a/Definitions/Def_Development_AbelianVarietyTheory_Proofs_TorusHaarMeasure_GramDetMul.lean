-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:12.149857+00:00
-- url     : https://prove2.me/theorems/0d7a4e51-f1cc-4592-a48d-63cdcc3c0dc7
-- title:
--   Gram Det Mul
-- statement:
--   Definitions and structural lemmas for Gram Det Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_AbsNormEqProdCmTypeSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
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
namespace GlobalTheory.ValMul
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.ValMul


