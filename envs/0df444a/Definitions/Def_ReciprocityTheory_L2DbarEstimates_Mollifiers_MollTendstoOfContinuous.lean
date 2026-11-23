-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous
-- name    : ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:56.568534+00:00
-- url     : https://prove2.me/theorems/d808a7b0-bedd-4e19-ab02-29359132b25a
-- title:
--   Moll Tendsto Of Continuous
-- statement:
--   Definitions and structural lemmas for Moll Tendsto Of Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollTendstoOfContinuous.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
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
end ReciprocityTheory.L2DbarEstimates.B


