-- Prove2me | solution 1 for AME125.cutInj_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:44.391264+00:00
-- url     : https://prove2.me/submissions/6c80c0ba-adf8-4848-8c61-2c7d4c6ab6c7

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
public import Theorems.Thm_AME125_U_add_transpose
public import Theorems.Thm_AME125_certs_ok
public import Theorems.Thm_AME125_certs_masks
public import Theorems.Thm_AME125_certOK_sum
public import Theorems.Thm_AME125_cutInj_of_inverse
public import Theorems.Thm_AME125_testBit_maskOf
public import Theorems.Thm_AME125_maskOf_lt
public import Theorems.Thm_AME125_popcount_maskOf
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
theorem _root_.solution (A : Finset (Fin 12)) (hA : A.card = 6) : CutInj (U + Uᵀ) A := by
  have hm : maskOf A ∈ certs.map Prod.fst := by
    rw [certs_masks, List.mem_filter, List.mem_range]
    exact ⟨maskOf_lt A, by simp [popcount_maskOf, hA]⟩
  obtain ⟨⟨m, L⟩, hc, hmL⟩ := List.mem_map.mp hm
  simp only at hmL
  subst hmL
  have hok : certOK (maskOf A, L) = true := List.all_eq_true.mp certs_ok _ hc
  refine cutInj_of_inverse _ A (fun j k ↦ (certN (maskOf A) L j k : ZMod 5)) fun i hi k hk ↦ ?_
  rw [← certOK_sum hok i k ((testBit_maskOf A i).mpr hi) ((testBit_maskOf A k).mpr hk)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ A
  · simp [hj, (testBit_maskOf A j).mpr hj]
  · have hb : (maskOf A).testBit j.1 = false :=
      Bool.eq_false_iff.mpr (mt (testBit_maskOf A j).mp hj)
    rw [if_neg hj, hb, if_neg Bool.false_ne_true,
      U_add_transpose i j fun h ↦ hj (h ▸ hi)]
end AME125
