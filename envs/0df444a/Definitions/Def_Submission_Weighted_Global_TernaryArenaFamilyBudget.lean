-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
-- name    : Submission_Weighted_Global_TernaryArenaFamilyBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:24:24.63099+00:00
-- url     : https://prove2.me/theorems/fabf2350-d7de-4e89-b5ac-9a20d900a6f6
-- title:
--   Ternary Arena Family Budget
-- statement:
--   Definitions and structural lemmas for Ternary Arena Family Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
def seedAt (e : (E×E)≃Fin N) (i : ℕ) : E×E := if hi : i<N then e.symm ⟨i,hi⟩ else (0,0)
def family (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ) :
    Family (config p (r+1) I A 0) :=
  WeightedGlobalArenaSeedCandidate.family maps τ cap U V scoreBound Q I A
    (fun k => data I A r b k ℓ (seedAt e k) row (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) rows catalog) L R
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
abbrev D := family maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog
def budgetGood {C : Config} [Fact C.p.Prime] (D : Family C) (p m F r K n U0 : ℕ) (i : ℕ) : Prop :=
  LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    (p^(r+1)) (p^(r+1)) ((p^(2*K))^(r+1))
    (9^(r+1)*n^2) (9^(r+1)*n^2) (scale m r K*(9*pairFactor m F K)^(r+1)*U0) i
end ThreeSum.WeightedGlobalArenaFamilyBudget


