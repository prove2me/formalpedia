-- Prove2me | solution 1 for Auto.aux_log_holder_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:27.014444+00:00
-- url     : https://prove2.me/submissions/7b7dc179-2fa3-4903-835e-a7610bdb11c8

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ∫⁻ z, ‖a z‖ₑ * ‖z * deriv a z‖ₑ ∂aux_logarithmicMeasure α β ≤
      aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by
  have hameas : AEStronglyMeasurable a (aux_logarithmicMeasure α β) :=
    AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict (Set.Icc α β))
        (fun t ↦ ENNReal.ofReal t⁻¹))
      (ha.continuousOn.aestronglyMeasurable measurableSet_Icc)
  have hdmeas : AEStronglyMeasurable (fun z ↦ z * deriv a z)
      (aux_logarithmicMeasure α β) :=
    (measurable_id.mul (measurable_deriv a)).aestronglyMeasurable
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
    hameas hdmeas (· * ·) 1
    (Filter.Eventually.of_forall fun _ ↦ by simp)
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  simpa [aux_logarithmicL2, enorm_mul] using h
end Auto
