-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:01:19.367428+00:00
-- url     : https://prove2.me/theorems/58ac8e24-f86c-4449-b0f7-d25d86bda3f8
-- title:
--   PreparedBudget
-- statement:
--   Definitions and structural lemmas for PreparedBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


