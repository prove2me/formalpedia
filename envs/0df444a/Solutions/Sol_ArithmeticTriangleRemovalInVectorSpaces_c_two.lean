-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.c_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:03.556592+00:00
-- url     : https://prove2.me/submissions/b71c5990-bab1-4cb9-ba43-165f528623f7

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SmallPrimes
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_rpow_one_sub_c
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_one_sub_c_le

section
public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
private lemma c_eq_one_sub_logb {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (h : ∀ x : ℝ, 0 < x → x < 1 → a ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, a ^ j ≤
      x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    c p = 1 - Real.logb p (a ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, a ^ j) := by
  rw [← le_antisymm (rpow_one_sub_c_le hp ha₀ ha₁) (le_rpow_one_sub_c hp h),
    Real.logb_rpow (by positivity) (by exact_mod_cast (by grind : p ≠ 1))]
  ring
private lemma rpow_mul_one_add_le {x : ℝ} (hx : 0 < x) :
    (1 / 2 : ℝ) ^ (-(1 / 3) : ℝ) * (3 / 2) ≤ x ^ (-(1 / 3) : ℝ) * (1 + x) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 / 3) (w₂ := 1 / 3)
    (p₁ := 3 / 2) (p₂ := 3 / 2 * (x / (1 / 2))) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← Real.rpow_add (by norm_num),
    (by norm_num : (2 / 3 : ℝ) + 1 / 3 = 1), Real.rpow_one,
    (by field_simp : 2 / 3 * (3 / 2 : ℝ) + 1 / 3 * (3 / 2 * (x / (1 / 2))) = 1 + x),
    Real.div_rpow hx.le (by norm_num), mul_div_assoc', div_le_iff₀ (by positivity)] at h
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg hx.le, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution : c 2 = 5 / 3 - Real.logb 2 3 := by
  rw [c_eq_one_sub_logb le_rfl (a := 1 / 2) (by norm_num) (by norm_num) ?_]
  · norm_num [sum_range_succ]
    rw [Real.logb_mul (by positivity) (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos
      (by norm_num), Real.logb_div (by norm_num) (by norm_num), Real.logb_div (by norm_num)
      (by norm_num), Real.logb_one, Real.logb_self_eq_one (by norm_num)]
    ring
  · intro x hx₀ hx₁
    norm_num [sum_range_succ]
    exact rpow_mul_one_add_le hx₀
end ArithmeticTriangleRemovalInVectorSpaces
