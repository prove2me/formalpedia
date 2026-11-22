-- Prove2me | solution 1 for Auto.norm_weight_sin_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:02:47.504471+00:00
-- url     : https://prove2.me/submissions/f62fe61f-ae23-4389-92b4-ae6a1eea877f

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_abs_sin_mul_div_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution (v t : ℝ) :
    ‖((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ)‖ ≤ |v| * carlesonWeight t := by
  rw [Complex.norm_real, Real.norm_eq_abs, mul_div_assoc, abs_mul,
    abs_of_nonneg (carlesonWeight_nonneg t), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_sin_mul_div_le v t) (carlesonWeight_nonneg t)
end Auto
