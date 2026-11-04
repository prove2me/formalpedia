-- Prove2me | Definitions.Def_Submission_Weighted_PreparedBudget
-- name    : Submission_Weighted_PreparedBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:45:56.475197+00:00
-- url     : https://prove2.me/theorems/3021675e-7a4a-43e3-a4d9-eb428293b202
-- title:
--   Prepared Budget
-- statement:
--   Definitions and structural lemmas for Prepared Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean

import Definitions.Def_Submission_Weighted_QueryBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
def width (N : ℕ) (f g : Config) : ℕ :=
  N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3
def queryMax (m : ℕ) (f g : Config) : ℕ := by
  classical
  exact (Finset.univ.filter (fun Q : TritWord (fixedLength m) => HasType Q (fixedPi m))).sup
    (fun Q => LightWeightedPreparedWanted.time f g Q)
end ThreeSum.WeightedPreparedBudget


