-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:59:07.650617+00:00
-- url     : https://prove2.me/theorems/dae61bb6-90b3-4442-be37-bc346d542e4d
-- title:
--   QueryBudget
-- statement:
--   Definitions and structural lemmas for QueryBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/QueryBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters_e1ae71d
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
def envelope (m : ℕ) : ℝ := exp ((fixedLength m : ℝ)*Qn)/zRoot^2739
end ThreeSum.WeightedQueryBudget
end
end WeightedCache3SUMRefinement_e1ae71d


