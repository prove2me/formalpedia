-- Prove2me | solution 1 for AME125.graphState_isNormalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:51.508813+00:00
-- url     : https://prove2.me/submissions/a5adf112-042d-4fef-9a69-5f80a086d5a2

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_isNormalized_iff_norm_sq_eq_one
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
theorem _root_.solution {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    IsNormalized (graphState U) := by
  rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq]
  have h : ∀ x : Config n 5, ‖(graphState U).ofLp x‖ ^ 2 = ((5 : ℝ) ^ n)⁻¹ := by
    intro x
    obtain ⟨k, rfl⟩ := hn
    simp only [graphState, ← two_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀, mkStateVector_apply, Complex.norm_mul, norm_inv, norm_pow,
      Complex.norm_ofNat, AddChar.norm_apply, mul_one, inv_pow, pow_mul, inv_inj]
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [h]
  simp
end AME125
