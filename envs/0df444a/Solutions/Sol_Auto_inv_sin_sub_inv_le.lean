-- Prove2me | solution 1 for Auto.inv_sin_sub_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:53.349155+00:00
-- url     : https://prove2.me/submissions/9c9b5e25-d55f-47dd-935a-507ef5502a21

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {y : ℝ} (hy : 0 < y) (hy' : y ≤ π / 2) :
    0 ≤ 1 / Real.sin y - 1 / y ∧ 1 / Real.sin y - 1 / y ≤ 1 := by
  have hs₁ : 2 / π * y ≤ Real.sin y := Real.mul_le_sin hy.le hy'
  have hπ := Real.pi_pos
  have hπ₄ := Real.pi_le_four
  have hs₀ : 0 < Real.sin y := lt_of_lt_of_le (by positivity) hs₁
  have hs₂ : Real.sin y ≤ y := Real.sin_le hy.le
  have hs₃ : y - y ^ 3 / 6 ≤ Real.sin y := Real.sin_ge_sub_cube hy.le
  refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le hs₀ hs₂), ?_⟩
  rw [div_sub_div _ _ hs₀.ne' hy.ne', div_le_one (by positivity)]
  have h₁ : y ^ 3 / 6 * π ≤ 2 * y * y := by
    have : y * π ≤ 12 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr this)]
  have h₂ : 2 / π * y * y ≤ Real.sin y * y := mul_le_mul_of_nonneg_right hs₁ hy.le
  have h₃ : y ^ 3 / 6 ≤ 2 / π * y * y := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]
    linarith
  nlinarith
end Auto
