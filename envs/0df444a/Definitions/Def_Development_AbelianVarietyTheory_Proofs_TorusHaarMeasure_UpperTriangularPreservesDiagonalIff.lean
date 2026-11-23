-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UpperTriangularPreservesDiagonalIff
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UpperTriangularPreservesDiagonalIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:14.113486+00:00
-- url     : https://prove2.me/theorems/06b3fbac-0c9a-41e4-8a52-19bc3190fc05
-- title:
--   Upper Triangular Preserves Diagonal Iff
-- statement:
--   Definitions and structural lemmas for Upper Triangular Preserves Diagonal Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/UpperTriangularPreservesDiagonalIff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
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
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory


