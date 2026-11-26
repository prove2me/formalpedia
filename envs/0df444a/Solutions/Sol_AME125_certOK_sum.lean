-- Prove2me | solution 1 for AME125.certOK_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:19:32.039418+00:00
-- url     : https://prove2.me/submissions/7ddf01ed-798a-472b-aa5a-722222301017

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
public import Theorems.Thm_AME125_sum_range_twelve
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
theorem _root_.solution {c : ℕ × List ℕ} (hc : certOK c = true) (i k : Fin 12)
    (hi : c.1.testBit i.1 = true) (hk : c.1.testBit k.1 = true) :
    ∑ j : Fin 12, (if c.1.testBit j.1 then 0 else theta i j * (certN c.1 c.2 j k : ZMod 5)) =
      if i = k then 1 else 0 := by
  have h : entryN c.1 c.2 i k % 5 = if i.1 = k.1 then 1 else 0 := by
    simp only [certOK, List.all_eq_true, List.mem_range] at hc
    simpa [hi, hk] using hc i.1 i.2 k.1 k.2
  have hcast : ((entryN c.1 c.2 i k : ℕ) : ZMod 5) =
      ∑ j : Fin 12, (if c.1.testBit j.1 then 0 else theta i j * (certN c.1 c.2 j k : ZMod 5)) := by
    rw [entryN, sum_range_twelve, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp [theta]
  rw [← hcast, ← ZMod.natCast_mod, h]
  by_cases hik : i = k
  · simp [hik]
  · simp [hik, Fin.val_ne_iff.mpr hik]
end AME125
