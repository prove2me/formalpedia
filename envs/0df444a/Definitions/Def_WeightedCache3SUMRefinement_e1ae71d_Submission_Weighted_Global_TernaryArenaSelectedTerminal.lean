-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:48:26.793193+00:00
-- url     : https://prove2.me/theorems/b3078d64-aa7b-4f59-b5ef-9e6c451d6063
-- title:
--   TernaryArenaSelectedTerminal
-- statement:
--   Definitions and structural lemmas for TernaryArenaSelectedTerminal, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSelectedTerminal.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedBudgetCollision
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSelectedTerminal
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaSelectedBudgets
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
def hashMap (A : Inputs) (s : State (p := p) A) (r : ℕ) :
    (Fin (A.J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p) :=
  LinearMap.pi (fun j => s.row j.val)
def input (I : Input) (A : Inputs) (s : State (p := p) A) (L R O : ℕ→ℕ→ℤ) (r : ℕ) : Input :=
  WeightedGlobalArenaPrefixGroups.input I (fun i t => L i t.val) (fun i t => R i t.val) s.row
    (root s.row (fun i t => O i t.val)) r
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (K n U0 : ℕ) (L R O : ℕ→ℕ→ℤ) (r : ℕ) (s : State (p := p) A)
end ThreeSum.WeightedGlobalArenaSelectedTerminal
end
end WeightedCache3SUMRefinement_e1ae71d


