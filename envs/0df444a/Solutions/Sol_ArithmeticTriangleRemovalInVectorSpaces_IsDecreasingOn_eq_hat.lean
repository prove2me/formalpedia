-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_hat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:29.889655+00:00
-- url     : https://prove2.me/submissions/8984033a-d7c8-4f30-96c2-d46d5ce02b94

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_eq_zero_of_lt
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples



set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsDecreasingOn
theorem _root_.solution (h : IsDecreasingOn N π) :
    π = hat N fun k ↦ (k + 1) * (π k - π (k + 1)) := by
  ext j
  have hterm (k : ℕ) : (k + 1 : ℝ) * (π k - π (k + 1)) * unif k j =
      if j ≤ k then π k - π (k + 1) else 0 := by
    unfold unif
    grind
  simp only [hat, hterm]
  by_cases hj : j ≤ N
  · rw [← sum_range_add_sum_Ico _ (by grind : j ≤ N + 1), sum_eq_zero fun k hk ↦ by grind,
      zero_add, sum_Ico_eq_sum_range]
    simp only [le_add_iff_nonneg_right, zero_le, ite_true, add_assoc j]
    rw [sum_range_sub' (fun k ↦ π (j + k)), add_zero, (by grind : j + (N + 1 - j) = N + 1),
      h.eq_zero_of_lt (Nat.lt_succ_self N), sub_zero]
  · rw [h.eq_zero_of_lt (by grind)]
    symm
    apply sum_eq_zero
    grind
end IsDecreasingOn
end ArithmeticTriangleRemovalInVectorSpaces
