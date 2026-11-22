-- Prove2me | Definitions.Def_Comp_SafetyChainQ
-- name    : Comp_SafetyChainQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:35:40.12283+00:00
-- url     : https://prove2.me/theorems/3e5bef70-c69f-4b4b-85d1-0adf7684bad4
-- title:
--   Safety Chain Q
-- statement:
--   Definitions and structural lemmas for Safety Chain Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_aF
import Theorems.Thm_Comp_CsgQ_mem_apre1F
import Theorems.Thm_Comp_CsgQ_mem_bF
import Theorems.Thm_Comp_CsgQ_mem_gStepF
import Theorems.Thm_Comp_CsgQ_mem_lpre1F
import Theorems.Thm_Comp_CsgQ_mem_pre1F
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.CsgQ.castIcc_coe
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_aF
attribute [local simp] Comp.CsgQ.mem_apre1F
attribute [local simp] Comp.CsgQ.mem_bF
attribute [local simp] Comp.CsgQ.mem_gStepF
attribute [local simp] Comp.CsgQ.mem_lpre1F
attribute [local simp] Comp.CsgQ.mem_pre1F
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
open Csg
inductive Chain
  | c0
  | c1
  | d0
  | d1
  | d2
  | bad
  deriving DecidableEq, Inhabited, Repr
instance : Fintype Chain where
  elems := {Chain.c0, Chain.c1, Chain.d0, Chain.d1, Chain.d2, Chain.bad}
  complete := by intro x; cases x <;> decide
def dirac (t : Chain) : Chain → ℚ := fun s' => if s' = t then 1 else 0
theorem dirac_nonneg (t s' : Chain) : 0 ≤ dirac t s' := by
  unfold dirac
  split_ifs <;> norm_num
theorem sum_dirac (t : Chain) : ∑ s' : Chain, dirac t s' = 1 := by
  unfold dirac
  simp
def coin (t u : Chain) : Chain → ℚ := fun s' => 1 / 2 * dirac t s' + 1 / 2 * dirac u s'
theorem coin_nonneg (t u s' : Chain) : 0 ≤ coin t u s' := by
  unfold coin
  have h1 := dirac_nonneg t s'
  have h2 := dirac_nonneg u s'
  linarith
theorem sum_coin (t u : Chain) : ∑ s' : Chain, coin t u s' = 1 := by
  unfold coin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_dirac, sum_dirac]
  norm_num
def chainK : Chain → Bool → Bool → (Chain → ℚ)
  | .c0, true, _ => coin .c0 .c1
  | .c0, false, _ => dirac .bad
  | .c1, _, true => dirac .c0
  | .c1, _, false => coin .c0 .c1
  | .d0, true, _ => dirac .d1
  | .d0, false, _ => dirac .bad
  | .d1, _, _ => dirac .d2
  | .d2, _, _ => dirac .bad
  | .bad, _, _ => dirac .bad
def chainGame : CsgQ Chain Bool Bool where
  K := chainK
  r := fun _ _ _ => 0
theorem chainK_cases (s : Chain) (a1 a2 : Bool) :
    (∃ t, chainGame.K s a1 a2 = dirac t) ∨ (∃ t u, chainGame.K s a1 a2 = coin t u) := by
  cases s <;> cases a1 <;> cases a2 <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
theorem chainGame_wf : chainGame.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · rcases chainK_cases s a1 a2 with ⟨t, ht⟩ | ⟨t, u, ht⟩
    · rw [ht]; exact dirac_nonneg t s'
    · rw [ht]; exact coin_nonneg t u s'
  · rcases chainK_cases s a1 a2 with ⟨t, ht⟩ | ⟨t, u, ht⟩
    · rw [ht]; exact sum_dirac t
    · rw [ht]; exact sum_coin t u
def chainSupp : Chain → Bool → Bool → Finset Chain
  | .c0, true, _ => {.c0, .c1}
  | .c0, false, _ => {.bad}
  | .c1, _, true => {.c0}
  | .c1, _, false => {.c0, .c1}
  | .d0, true, _ => {.d1}
  | .d0, false, _ => {.bad}
  | .d1, _, _ => {.d2}
  | .d2, _, _ => {.bad}
  | .bad, _, _ => {.bad}
def chainSafe : Finset Chain := {.c0, .c1, .d0, .d1, .d2}
def pre1C (x : Finset Chain) : Finset Chain :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, chainSupp s a1 a2 ⊆ x
def chainR2 : Finset Chain := {.c0, .c1, .d0, .d1}
def chainR3 : Finset Chain := {.c0, .c1, .d0}
def chainGood : Finset Chain := {.c0, .c1}
end Comp


