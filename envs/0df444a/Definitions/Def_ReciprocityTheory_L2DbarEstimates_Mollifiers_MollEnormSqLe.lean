-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
-- name    : ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:46.689134+00:00
-- url     : https://prove2.me/theorems/baba777d-603e-4268-a2f9-c32b46935d3b
-- title:
--   Moll Enorm Sq Le
-- statement:
--   Definitions and structural lemmas for Moll Enorm Sq Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Mollifiers/MollEnormSqLe.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
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


