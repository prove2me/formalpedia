-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenMain
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:19:52.415303+00:00
-- url     : https://prove2.me/theorems/88e21374-0dbb-43e4-ac05-d729f182793e
-- title:
--   FrozenMain
-- statement:
--   Definitions and structural lemmas for FrozenMain, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenMain.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenTime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_cost_update_drop

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost cost_update_drop)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedFrozenQuery
end WeightedCache3SUMRefinement_e1ae71d


