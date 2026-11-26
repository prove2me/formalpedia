-- Prove2me | solution 1 for Auto.aux_log_weight_conversion_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:33.741991+00:00
-- url     : https://prove2.me/submissions/31125543-a11d-47ed-ab7a-fefc15833673

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_enorm_mul_inv_cancel
public import Theorems.Thm_Auto_aux_restrict_logarithmicMeasure_Ioc

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (hx : 0 < x)
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) (a d : ℝ → ℝ) :
    ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖d z‖ₑ =
      ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖z * d z‖ₑ
        ∂aux_logarithmicMeasure α β := by
  rw [show (aux_logarithmicMeasure α β).restrict (Set.Ioc x y) =
      (volume.restrict (Set.Ioc x y)).withDensity fun t ↦ ENNReal.ofReal t⁻¹ by
        exact aux_restrict_logarithmicMeasure_Ioc hsub]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
    have hzpos : 0 < z := hx.trans hz.1
    change ‖a z‖ₑ * ‖d z‖ₑ =
      ENNReal.ofReal z⁻¹ * (‖a z‖ₑ * ‖z * d z‖ₑ)
    rw [show ENNReal.ofReal z⁻¹ * (‖a z‖ₑ * ‖z * d z‖ₑ) =
        ‖a z‖ₑ * (ENNReal.ofReal z⁻¹ * ‖z * d z‖ₑ) by ring]
    rw [aux_enorm_mul_inv_cancel hzpos]
  · exact (measurable_inv.comp measurable_id).ennreal_ofReal.aemeasurable
  · exact ae_of_all _ fun _ ↦ lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
end Auto
