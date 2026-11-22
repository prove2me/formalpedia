-- Prove2me | solution 1 for Auto.abs_inv_sin_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:53:34.192544+00:00
-- url     : https://prove2.me/submissions/76516448-50a6-496d-abe4-60ca773fb037

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_inv_sin_sub_inv_le
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |1 / Real.sin (π * s) - 1 / (π * s)| ≤ 1 := by
  have hπ := Real.pi_pos
  rcases lt_trichotomy s 0 with h | rfl | h
  · have := inv_sin_sub_inv_le (y := π * -s) (by nlinarith)
      (by rw [abs_of_neg h] at hs; nlinarith)
    rw [mul_neg, Real.sin_neg, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div] at this
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  · simp
  · have := inv_sin_sub_inv_le (y := π * s) (by positivity)
      (by rw [abs_of_pos h] at hs; nlinarith)
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
end Auto
