-- Prove2me | solution 1 for AME125.testBit_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:32.309263+00:00
-- url     : https://prove2.me/submissions/cc26122a-8146-43db-a12f-b5e85479c6f5

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
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
open scoped Matrix
namespace AME125
theorem _root_.solution (A : Finset (Fin 12)) (i : Fin 12) :
    (maskOf A).testBit i.1 = true ↔ i ∈ A := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, maskOf, Finset.toFinset_bitIndices_sum_two_pow]
  simp [Fin.val_inj]
end AME125
