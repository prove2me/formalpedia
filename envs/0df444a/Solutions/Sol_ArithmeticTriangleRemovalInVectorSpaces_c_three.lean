-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.c_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:07.532644+00:00
-- url     : https://prove2.me/submissions/c86c2a2e-907a-4916-9de5-0fb2f78ffd15

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
private lemma div_rpow_two_div_three_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hw : 4 * a ^ 2 + a - 2 = 0) :
    (x / a) ^ (2 / 3 : ℝ) ≤ (1 + x + x ^ 2) / (1 + a + a ^ 2) := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / (1 + a + a ^ 2))
    (w₂ := a / (1 + a + a ^ 2)) (w₃ := a ^ 2 / (1 + a + a ^ 2)) (p₁ := 1) (p₂ := x / a)
    (p₃ := (x / a) ^ 2) (by positivity) (by positivity) (by positivity) zero_le_one
    (by positivity) (by positivity) (by field_simp)
  rw [Real.one_rpow, one_mul, ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_add (by positivity)] at h
  convert h using 2
  · field_simp
    push_cast
    linarith
  · field_simp
private lemma rpow_mul_one_add_add_sq_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hw : 4 * a ^ 2 + a - 2 = 0) :
    a ^ (-(2 / 3) : ℝ) * (1 + a + a ^ 2) ≤ x ^ (-(2 / 3) : ℝ) * (1 + x + x ^ 2) := by
  have h := div_rpow_two_div_three_le ha hx hw
  rw [Real.div_rpow hx.le ha.le, div_le_div_iff₀ (by positivity) (by positivity)] at h
  rw [Real.rpow_neg ha.le, Real.rpow_neg hx.le, inv_mul_eq_div, inv_mul_eq_div,
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
theorem _root_.solution {a : ℝ} (ha : a = (√33 - 1) / 8) :
    c 3 = 1 - Real.log (a ^ (-2 / 3 : ℝ) + a ^ (1 / 3 : ℝ) + a ^ (4 / 3 : ℝ)) / Real.log 3 := by
  have h33 : √33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  obtain ⟨ha₀, ha₁⟩ : 0 < a ∧ a < 1 := by
    rw [ha]
    constructor <;> nlinarith [Real.sqrt_nonneg 33]
  rw [c_eq_one_sub_logb (by norm_num) ha₀ ha₁ ?_]
  · norm_num [sum_range_succ]
    rw [Real.logb, mul_add, mul_add, mul_one, ← Real.rpow_add_one ha₀.ne',
      ← Real.rpow_add_natCast ha₀.ne']
    norm_num
  · intro x hx₀ hx₁
    norm_num [sum_range_succ]
    apply rpow_mul_one_add_add_sq_le ha₀ hx₀
    rw [ha]
    linear_combination h33 / 16
end ArithmeticTriangleRemovalInVectorSpaces
