-- Prove2me | solution 1 for Auto.norm_carlesonOp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:40.401602+00:00
-- url     : https://prove2.me/submissions/ab33aaad-30c3-4d92-bb7d-ef86e987adbf

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_integrable_carlesonWeight
public import Theorems.Thm_Auto_norm_weight_sin_div_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {h : ℝ → ℂ} {ν : ℝ → ℝ} {B V : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (hV : ∀ x, |ν x| ≤ V) (x : ℝ) :
    ‖carlesonOp h ν x‖ ≤ B * V * ∫ t, carlesonWeight t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc ‖carlesonOp h ν x‖ ≤ ∫ t, B * |ν x| * carlesonWeight t :=
        norm_integral_le_of_norm_le (integrable_carlesonWeight.const_mul _)
          (ae_of_all _ fun t => by
            rw [norm_mul, mul_assoc]
            exact mul_le_mul (hB _) (norm_weight_sin_div_le _ t) (norm_nonneg _) hB0)
    _ ≤ B * V * ∫ t, carlesonWeight t := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hV x) hB0)
          (integral_nonneg carlesonWeight_nonneg)
end Auto
