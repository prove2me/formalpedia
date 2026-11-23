-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyTw
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyTw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:33.120645+00:00
-- url     : https://prove2.me/theorems/17f9903c-9f27-405f-8399-b04fce908a8b
-- title:
--   Apply Tw
-- statement:
--   Definitions and structural lemmas for Apply Tw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyTw.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
end ReciprocityTheory.L2DbarEstimates.I


