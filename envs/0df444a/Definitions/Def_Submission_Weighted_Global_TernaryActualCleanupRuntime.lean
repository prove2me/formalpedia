-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
-- name    : Submission_Weighted_Global_TernaryActualCleanupRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:21:13.677137+00:00
-- url     : https://prove2.me/theorems/a5e04cb2-a5a1-46af-ad75-58626983e956
-- title:
--   Ternary Actual Cleanup Runtime
-- statement:
--   Definitions and structural lemmas for Ternary Actual Cleanup Runtime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
def collisions (keys : ℕ→ℕ) (n : ℕ) : ℕ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin n=>keys i.val)).card
end ThreeSum.WeightedGlobalActualCleanupRuntime


