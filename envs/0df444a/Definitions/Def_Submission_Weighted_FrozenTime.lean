-- Prove2me | Definitions.Def_Submission_Weighted_FrozenTime
-- name    : Submission_Weighted_FrozenTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:46.886752+00:00
-- url     : https://prove2.me/theorems/40535389-9ff6-4c18-9f39-e4c90823530b
-- title:
--   Frozen Time
-- statement:
--   Definitions and structural lemmas for Frozen Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
namespace ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def queryTime {N : ℕ} (L T K : ℕ) (R : TritWord N) : ℕ :=
  10000*(N+L+1)*work T (coords N K) R
end ThreeSum.LightWeightedFrozenQuery


