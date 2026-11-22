-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.le_rpow_one_sub_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:12.17282+00:00
-- url     : https://prove2.me/submissions/dba3032a-59a9-4a8d-ae5e-830b5b92ef6d

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_three_div_two_le_rpow_mul_sum
section
@[expose] public section
open Finset Filter Topology
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}
private lemma rpow_one_sub_c (hp : 2 ≤ p) :
    (p : ℝ) ^ (1 - c p) =
      ⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [c, sub_sub_cancel, Real.rpow_logb (by positivity)
    (by exact_mod_cast (by grind : p ≠ 1))]
  refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (le_ciInf ?_)
  rintro ⟨x, hx₀, hx₁⟩
  exact three_div_two_le_rpow_mul_sum hp hx₀ hx₁
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hp : 2 ≤ p) {b : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 → b ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    b ≤ (p : ℝ) ^ (1 - c p) := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [rpow_one_sub_c hp]
  apply le_ciInf
  rintro ⟨x, hx₀, hx₁⟩
  exact h x hx₀ hx₁
end ArithmeticTriangleRemovalInVectorSpaces
