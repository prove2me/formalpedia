-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.c_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:56.90981+00:00
-- url     : https://prove2.me/submissions/3d46c4f8-123c-4753-bb3d-2bb1b851d57f

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_one_sub_c_le
section
@[expose] public section
open Finset Filter Topology
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}
private lemma exists_rpow_mul_sum_lt (hp : 2 ≤ p) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j < p := by
  have hderiv : HasDerivAt (fun x : ℝ ↦ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j)
      (p * (p - 1) / 6) 1 := by
    have h := sum_range_id_mul_two p
    rw [← Nat.cast_inj (R := ℝ)] at h
    push_cast [Nat.cast_sub (by grind : 1 ≤ p)] at h
    convert! (Real.hasDerivAt_rpow_const (p := -((p : ℝ) - 1) / 3) (Or.inl one_ne_zero)).fun_mul
      (HasDerivAt.fun_sum fun j (_ : j ∈ range p) ↦ hasDerivAt_pow j (1 : ℝ)) using 1
    try simp
    linarith
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
    (nhdsWithin_mono _ fun y (hy : y ∈ Set.Iio 1) ↦ hy.ne)
  obtain ⟨x, hslope, hx₀, hx₁⟩ := ((hslope.eventually (lt_mem_nhds
    (by nlinarith [(Nat.ofNat_le_cast.2 hp : (2 : ℝ) ≤ p)] : (0 : ℝ) < p * (p - 1) / 6))).and
    (Ioo_mem_nhdsLT one_pos)).exists
  refine ⟨x, hx₀, hx₁, ?_⟩
  rw [slope_def_field, lt_div_iff_of_neg (by linarith), zero_mul, sub_neg] at hslope
  simpa using hslope
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
theorem _root_.solution (hp : 2 ≤ p) : 0 < c p := by
  obtain ⟨x, hx₀, hx₁, hx⟩ := exists_rpow_mul_sum_lt hp
  by_contra! hc
  have := Real.self_le_rpow_of_one_le (Nat.one_le_cast.2 (by grind) : (1 : ℝ) ≤ p)
    (by linarith : 1 ≤ 1 - c p)
  linarith [rpow_one_sub_c_le hp hx₀ hx₁]
end ArithmeticTriangleRemovalInVectorSpaces
