-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopABI
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopABI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:44:26.4409+00:00
-- url     : https://prove2.me/theorems/3681b4ea-a463-410c-9102-553887a71b4d
-- title:
--   TernaryColoredLoopABI
-- statement:
--   Definitions and structural lemmas for TernaryColoredLoopABI, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopABI.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredSolver
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


