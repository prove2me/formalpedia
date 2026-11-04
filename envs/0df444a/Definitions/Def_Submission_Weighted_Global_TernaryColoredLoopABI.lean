-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
-- name    : Submission_Weighted_Global_TernaryColoredLoopABI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:02:26.399238+00:00
-- url     : https://prove2.me/theorems/a0ab17ee-8018-4de4-b76d-c2bbaa40290f
-- title:
--   Ternary Colored Loop ABI
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop ABI, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopABI.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopABI
open Light WeightedGlobalArenaLayout WeightedGlobalArenaLoop LightWeightedGlobalColoredSolver WeightedGlobalLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000
def scalar (S : Setup p m F K N E) : ℕ :=
  m+F+p+fixedAlpha m 2+WeightedGlobalArenaSourceSetup.alphaRank m+TernaryCodeSemantics.address S.Q.val+
    S.wordRadix+S.alpha+S.beta+S.budgetScale+S.arrays.J+S.rounds
end ThreeSum.WeightedGlobalColoredLoopABI


