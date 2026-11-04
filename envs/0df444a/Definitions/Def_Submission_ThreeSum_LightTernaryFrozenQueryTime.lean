-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
-- name    : Submission_ThreeSum_LightTernaryFrozenQueryTime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:41.997776+00:00
-- url     : https://prove2.me/theorems/2d45a019-654c-4c37-8f56-8c9de50de588
-- title:
--   Light Ternary Frozen Query Time
-- statement:
--   Definitions and structural lemmas for Light Ternary Frozen Query Time, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
namespace ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000
def queryTime {N : ℕ} (L T K : ℕ) (R : TritWord N) : ℕ :=
  10000*(N+L+1)*work T (coords N K) R
end ThreeSum.LightTernaryFrozenQuery


