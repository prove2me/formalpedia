-- Prove2me | solution 1 for Auto.abs_sin_mul_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:38:49.096519+00:00
-- url     : https://prove2.me/submissions/66054830-baf6-4716-a3b5-8b9063c72576

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (v t : ℝ) : |Real.sin (v * t) / t| ≤ |v| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [abs_div, div_le_iff₀ (abs_pos.mpr ht), ← abs_mul]
  exact Real.abs_sin_le_abs
end Auto
