-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenTime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:09:25.735415+00:00
-- url     : https://prove2.me/theorems/af299492-68d5-4550-a608-3cf48f1245cc
-- title:
--   FrozenTime
-- statement:
--   Definitions and structural lemmas for FrozenTime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenTime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def queryTime {N : ℕ} (L T K : ℕ) (R : TritWord N) : ℕ :=
  10000*(N+L+1)*work T (coords N K) R
end ThreeSum.LightWeightedFrozenQuery
end WeightedCache3SUMRefinement_e1ae71d


