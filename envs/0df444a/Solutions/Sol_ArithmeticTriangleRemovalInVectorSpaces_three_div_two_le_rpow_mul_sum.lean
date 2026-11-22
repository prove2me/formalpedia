-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.three_div_two_le_rpow_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:17.269807+00:00
-- url     : https://prove2.me/submissions/c27e5203-7d78-4169-adf2-0cb980903d6d

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent

set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    3 / 2 ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by
  have hroot : x ^ (1 / 3 : ℝ) ≤ 1 + 1 / 3 * (x - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ x - 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have hneg : 3 / (2 + x) ≤ x ^ (-((p : ℝ) - 1) / 3) := by
    grw [← Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁.le
      (by linarith [(Nat.ofNat_le_cast.2 hp : (2 : ℝ) ≤ p)] : -((p : ℝ) - 1) / 3 ≤ -(1 / 3))]
    rw [Real.rpow_neg hx₀.le, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    linarith
  have hsum : 1 + x ≤ ∑ j ∈ range p, x ^ j := by
    grw [← sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hp) fun j _ _ ↦ by positivity]
    simp [add_comm]
  grw [← hneg, ← hsum]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith
end ArithmeticTriangleRemovalInVectorSpaces
