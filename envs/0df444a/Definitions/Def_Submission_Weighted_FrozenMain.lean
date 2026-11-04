-- Prove2me | Definitions.Def_Submission_Weighted_FrozenMain
-- name    : Submission_Weighted_FrozenMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:52:37.319727+00:00
-- url     : https://prove2.me/theorems/3d0f3cb8-46dc-4d7f-8d5c-f67a9092d24e
-- title:
--   Frozen Main
-- statement:
--   Definitions and structural lemmas for Frozen Main, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenMain.lean

import Definitions.Def_Submission_Weighted_FrozenTime
import Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_cost_update_drop

set_option autoImplicit false
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost cost_update_drop)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedFrozenQuery


