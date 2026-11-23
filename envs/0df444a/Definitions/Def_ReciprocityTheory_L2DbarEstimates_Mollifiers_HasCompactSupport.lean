-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
-- name    : ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:24:18.501327+00:00
-- url     : https://prove2.me/theorems/52e01275-24b6-4696-9f4d-5554f42ef67c
-- title:
--   Has Compact Support
-- statement:
--   Definitions and structural lemmas for Has Compact Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/HasCompactSupport.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
end
end ReciprocityTheory.L2DbarEstimates.B


