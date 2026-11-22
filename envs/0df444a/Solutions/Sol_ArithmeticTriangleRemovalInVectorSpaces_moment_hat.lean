-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.moment_hat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:28.938679+00:00
-- url     : https://prove2.me/submissions/f609a36c-f099-46c9-97ee-c7a38014c0e9

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_range_succ_cast
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples


section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
private lemma sum_mul_unif (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range (N + 1), f j * unif k j = (∑ j ∈ range (k + 1), f j) / (k + 1) := by
  rw [← sum_range_add_sum_Ico _ (by grind : k + 1 ≤ N + 1), sum_eq_zero (s := Ico _ _),
    add_zero, div_eq_mul_inv, sum_mul]
  · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr with j
    simp [unif, j.is_le]
  · intro j hj
    simp only [mem_Ico] at hj
    simp [unif, (by grind : ¬j ≤ k)]
private lemma moment_unif (hk : k ≤ N) : moment N (unif k) = k / 2 := by
  rw [moment, sum_mul_unif hk, sum_range_succ_cast]
  field_simp
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (w : ℕ → ℝ) :
    moment N (hat N w) = (∑ k ∈ range (N + 1), (k : ℝ) * w k) / 2 := by
  simp only [moment, hat, mul_sum]
  rw [sum_comm, div_eq_mul_inv, sum_mul, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  congr with k
  simp_rw [mul_left_comm _ (w k), ← mul_sum]
  rw [← moment, moment_unif k.is_le]
  ring
end ArithmeticTriangleRemovalInVectorSpaces
