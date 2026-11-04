-- Prove2me | Definitions.Def_Submission_Weighted_QueryBudget
-- name    : Submission_Weighted_QueryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:43:00.469717+00:00
-- url     : https://prove2.me/theorems/faa66d8c-ac2e-4979-8920-ea3d9f6d06ce
-- title:
--   Query Budget
-- statement:
--   Definitions and structural lemmas for Query Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
def envelope (m : ℕ) : ℝ := exp ((fixedLength m : ℝ)*Qn)/zRoot^1024
end ThreeSum.WeightedQueryBudget


