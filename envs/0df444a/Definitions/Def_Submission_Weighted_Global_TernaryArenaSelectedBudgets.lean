-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
-- name    : Submission_Weighted_Global_TernaryArenaSelectedBudgets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:36:47.052408+00:00
-- url     : https://prove2.me/theorems/b99f3370-5666-4c66-b2b3-2cd7b5a90a6d
-- title:
--   Ternary Arena Selected Budgets
-- statement:
--   Definitions and structural lemmas for Ternary Arena Selected Budgets, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaSelectedBudgets
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
structure State (A : Inputs) where
  row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p
  rows : List (Fin A.J→ZMod p)
def initial (A : Inputs) : State (p := p) A := ⟨0,[]⟩
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)
def candidates (j : ℕ) (s : State (p := p) A) :=
  family maps τ cap U V scoreBound Q I A j b e ℓ s.row L R O s.rows (catalog j)
def chosen (j : ℕ) (s : State (p := p) A) : ℕ :=
  LightTernaryRowSelector.pick
    (budgetGood (candidates maps τ cap U V scoreBound Q I A b e ℓ L R O catalog j s) p m F j K n U0) N-1
def step (j : ℕ) (s : State (p := p) A) : State (p := p) A :=
  let seed := seedAt e (chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s)
  ⟨Function.update s.row j (TernaryOriginalRowMenu.row (A.J+2) ℓ seed),
    TernaryPhysicalDigitSpan.digitProjection A.J (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed)::s.rows⟩
def run : ℕ→State (p := p) A
  | 0 => initial A
  | j+1 => step maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j
      (run j)
structure Budget (j : ℕ) (s : State (p := p) A) : Prop where
  paired : (p^(2*K))^j*current maps τ cap I A s.row L R O Q j K≤(9*pairFactor m F K)^j*U0
  left : p^j*collisions A s.row L j I.nB≤9^j*n^2
  right : p^j*collisions A s.row R j I.nC≤9^j*n^2
  length : s.rows.length=j
end ThreeSum.WeightedGlobalArenaSelectedBudgets


