-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:51.208604+00:00
-- url     : https://prove2.me/theorems/24e5cbe1-fae5-4bc4-b83b-89ef369f6360
-- title:
--   Compact Space Real Unitary Group Of Definite
-- statement:
--   Definitions and structural lemmas for Compact Space Real Unitary Group Of Definite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactSpaceRealUnitaryGroupOfDefinite.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsCompactOrthBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
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
namespace GlobalTheory.FinCovol
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.FinCovol


