-- Prove2me | solution 1 for Auto.aux_pair_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:06.331467+00:00
-- url     : https://prove2.me/submissions/25c19a0a-52b7-4617-a09d-ad34b31c9c07

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_log_local_integral_eq
public import Theorems.Thm_Auto_aux_log_measure_le
public import Theorems.Thm_Auto_aux_derivmul_aemeasurable_local
public import Theorems.Thm_Auto_aux_cauchy_lintegral_two
public import Theorems.Thm_Auto_aux_half_mul_half_sq

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal ((β - α) / α) *
      ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure α β := by
  have hftc : ‖a y - a x‖ₑ ≤
      ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ∂aux_logarithmicMeasure α β := by
    rw [aux_log_local_integral_eq hα hx hy]
    exact enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
      (ha.mono (Icc_subset_Icc hx.1 hy.2)) hxy
  have hcs := aux_cauchy_lintegral_two
    (aux_derivmul_aemeasurable_local hαβ hx hy a ha)
  have hmeasure := aux_log_measure_le hα hx hy
  have hlin : ‖a y - a x‖ₑ ≤
      ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
        (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) := by
    calc
      ‖a y - a x‖ₑ ≤ ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ
          ∂aux_logarithmicMeasure α β := hftc
      _ ≤ (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) *
          (aux_logarithmicMeasure α β (Set.Icc x y)) ^ ((2 : ℝ)⁻¹) := by
        simpa only [Measure.restrict_apply_univ] using hcs
      _ ≤ (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) := by
        gcongr
      _ = ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
            ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) := mul_comm _ _
  calc
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤
        (ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
            ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = _ := aux_half_mul_half_sq _ _
end Auto
