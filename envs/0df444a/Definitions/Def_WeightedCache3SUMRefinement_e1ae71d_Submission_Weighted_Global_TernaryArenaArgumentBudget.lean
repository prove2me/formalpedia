-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentBudget
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:43:21.758536+00:00
-- url     : https://prove2.me/theorems/f73a190e-db4b-4c49-baaf-d858c13ebfec
-- title:
--   TernaryArenaArgumentBudget
-- statement:
--   Definitions and structural lemmas for TernaryArenaArgumentBudget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaArgumentWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters
def need (m p F M n U : ℕ) : Need :=
  let S := budget m p F 1 M 0 0 n U
  ⟨16*(S.word+S.depth+1)^2,0,0⟩
end ThreeSum.WeightedGlobalArenaArgumentBudget
end
end WeightedCache3SUMRefinement_e1ae71d


