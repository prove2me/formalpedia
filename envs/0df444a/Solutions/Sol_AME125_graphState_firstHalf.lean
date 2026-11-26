-- Prove2me | solution 1 for AME125.graphState_firstHalf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:41.746869+00:00
-- url     : https://prove2.me/submissions/0cf468b0-1b1a-48fc-bb36-684e2ef87f1c

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_AME125_lift_leftIndex
public import Theorems.Thm_AME125_reduced_graphState
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_maximallyMixed_apply
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
theorem _root_.solution {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : CutInj (U + Uᵀ) (firstHalf n (n / 2))) :
    HasMaximallyMixedFirstReduction (n / 2) (Nat.div_le_self n 2) (graphState U) := by
  have hm := Nat.div_le_self n 2
  have hk : n - n / 2 = n / 2 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  ext a b
  obtain ⟨K, hK0, hK⟩ := reduced_graphState hm U a b
  rw [hK, maximallyMixed_apply, card_config]
  by_cases hab : a = b
  · subst hab
    have h0 : coeff hm (U + Uᵀ) (toZ a - toZ a) = 0 := by
      funext k
      simp [coeff, lift]
    have h5 : ((5 : ℂ) ^ (n / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hK0 rfl, if_pos h0, if_pos rfl, hk]
    field_simp
    simp
  · have hne : coeff hm (U + Uᵀ) (toZ a - toZ b) ≠ 0 := by
      intro hc
      apply hab
      have hw := h (lift (toZ a - toZ b)) (fun i hi ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp [lift, hi]) (fun j hj ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          have hjk : rightIndex hm ⟨j.1 - n / 2, by omega⟩ = j := by
            ext
            simp [rightIndex]
            omega
          have := congrFun hc ⟨j.1 - n / 2, by omega⟩
          simpa [coeff, hjk] using this)
      funext i
      have hi := congrFun hw (leftIndex hm i)
      rw [lift_leftIndex] at hi
      exact sub_eq_zero.mp hi
    rw [if_neg hne, if_neg hab]
    ring
end AME125
