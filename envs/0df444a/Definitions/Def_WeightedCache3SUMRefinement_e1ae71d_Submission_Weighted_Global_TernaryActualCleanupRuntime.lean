-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualCleanupRuntime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualCleanupRuntime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:57:39.358474+00:00
-- url     : https://prove2.me/theorems/ea63daf3-9795-43ca-bf24-07e3a9c9c8d3
-- title:
--   TernaryActualCleanupRuntime
-- statement:
--   Definitions and structural lemmas for TernaryActualCleanupRuntime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
def collisions (keys : ℕ→ℕ) (n : ℕ) : ℕ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin n=>keys i.val)).card
end ThreeSum.WeightedGlobalActualCleanupRuntime
end
end WeightedCache3SUMRefinement_e1ae71d


