-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredQueryBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredQueryBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:07:33.866116+00:00
-- url     : https://prove2.me/theorems/949c9c3c-78ed-4ce5-b3f7-070f53d5aaba
-- title:
--   TernaryColoredQueryBudget
-- statement:
--   Definitions and structural lemmas for TernaryColoredQueryBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredQueryBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredQueryBudget
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def coefficient (P : Profile κ) : ℕ :=
  WeightedGlobalUniformQueryTime.coefficient P.m (256*(P.allocation.D+1)) P.allocation.E κ
end ThreeSum.WeightedGlobalColoredQueryBudget
end
end WeightedCache3SUMRefinement_e1ae71d


