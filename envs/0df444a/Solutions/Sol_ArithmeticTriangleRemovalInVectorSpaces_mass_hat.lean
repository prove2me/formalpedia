-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mass_hat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:26.13264+00:00
-- url     : https://prove2.me/submissions/8a09d44e-a551-49bb-9fac-b8d13ebf211d

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
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
private lemma mass_unif (hk : k ≤ N) : mass N (unif k) = 1 := by
  have h := sum_mul_unif hk fun _ ↦ 1
  simp only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  rw [mass, h]
  push_cast
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
theorem _root_.solution (w : ℕ → ℝ) : mass N (hat N w) = ∑ k ∈ range (N + 1), w k := by
  simp only [mass, hat]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  congr with k
  rw [← mul_sum, ← mass, mass_unif k.is_le, mul_one]
end ArithmeticTriangleRemovalInVectorSpaces
