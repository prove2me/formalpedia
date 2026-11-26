-- Prove2me | solution 1 for Auto.aux_chain_first_ftc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:33.983065+00:00
-- url     : https://prove2.me/submissions/13ccfffd-2512-476d-8350-daf7e5d47849

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_chain_sq_energy_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  let E : ℝ≥0∞ := ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
    ∂aux_logarithmicMeasure α β
  have hsquare := aux_chain_sq_energy_le hα hαβ a ha t ht
  have hroot :
      (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        (ENNReal.ofReal ((β - α) / α) * E) ^ ((2 : ℝ)⁻¹) := by
    apply ENNReal.rpow_le_rpow
    · simpa only [E] using hsquare
    · positivity
  have hELp : aux_logarithmicL2 α β (fun t ↦ t * deriv a t) = E ^ ((2 : ℝ)⁻¹) := by
    unfold aux_logarithmicL2 E
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
    have hsupport : (aux_logarithmicMeasure α β).restrict (Set.Icc α β) =
        aux_logarithmicMeasure α β := by
      unfold aux_logarithmicMeasure
      rw [restrict_withDensity measurableSet_Icc,
        Measure.restrict_restrict_of_subset Subset.rfl]
    rw [hsupport]
  calc
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) =
        (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
      simp only [← enorm_eq_nnnorm]
    _ ≤ (ENNReal.ofReal ((β - α) / α) * E) ^ ((2 : ℝ)⁻¹) := hroot
    _ = (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) * E ^ ((2 : ℝ)⁻¹) :=
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rw [hELp]
end Auto
