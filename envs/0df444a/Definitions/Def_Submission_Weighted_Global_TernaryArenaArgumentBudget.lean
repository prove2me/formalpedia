-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentBudget
-- name    : Submission_Weighted_Global_TernaryArenaArgumentBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:48:05.465622+00:00
-- url     : https://prove2.me/theorems/9a0dd8b0-71cd-426b-86e2-93d54001ce8e
-- title:
--   Ternary Arena Argument Budget
-- statement:
--   Definitions and structural lemmas for Ternary Arena Argument Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentWords
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters
def need (m p F M n U : ℕ) : Need :=
  let S := budget m p F 1 M 0 0 n U
  ⟨16*(S.word+S.depth+1)^2,0,0⟩
end ThreeSum.WeightedGlobalArenaArgumentBudget


