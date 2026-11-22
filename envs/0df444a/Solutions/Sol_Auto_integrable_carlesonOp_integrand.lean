-- Prove2me | solution 1 for Auto.integrable_carlesonOp_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:00.46827+00:00
-- url     : https://prove2.me/submissions/44536474-037f-4309-8cd3-34d9abc0f761

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_measurable_carlesonWeight
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
theorem _root_.solution {h : ℝ → ℂ} {B : ℝ} (hh : Measurable h)
    (hB : ∀ x, ‖h x‖ ≤ B) (v x : ℝ) :
    Integrable fun t => h (x - t) * ((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ) := by
  have hw := measurable_carlesonWeight
  refine (integrable_carlesonWeight.const_mul (B * |v|)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun t => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (hB _) (norm_weight_sin_div_le v t) (norm_nonneg _)
    ((norm_nonneg _).trans (hB 0))
end Auto
