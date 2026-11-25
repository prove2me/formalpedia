-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IntegralEqIntegralTsumOfLintegral
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IntegralEqIntegralTsumOfLintegral
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:08.90927+00:00
-- url     : https://prove2.me/theorems/a10cb03a-0d02-4258-9730-785f43b3772a
-- title:
--   Integral Eq Integral Tsum Of Lintegral
-- statement:
--   Definitions and structural lemmas for Integral Eq Integral Tsum Of Lintegral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IntegralEqIntegralTsumOfLintegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
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
namespace GlobalTheory.UnfoldComplex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.UnfoldComplex


