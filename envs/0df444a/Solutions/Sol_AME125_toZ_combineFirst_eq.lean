-- Prove2me | solution 1 for AME125.toZ_combineFirst_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:58.468362+00:00
-- url     : https://prove2.me/submissions/4a811caf-48ee-4bcb-b065-1fbde52b3b31

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_AME125_toZ_combineFirst_apply
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (a b : Config m 5) (z : Config (n - m) 5) :
    toZ (combineFirst m hm a z) = toZ (combineFirst m hm b z) + lift (toZ a - toZ b) := by
  funext i
  rw [Pi.add_apply, toZ_combineFirst_apply, toZ_combineFirst_apply]
  unfold lift
  split_ifs <;> simp
end AME125
