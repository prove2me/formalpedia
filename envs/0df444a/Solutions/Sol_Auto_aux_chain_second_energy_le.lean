-- Prove2me | solution 1 for Auto.aux_chain_second_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:51.840941+00:00
-- url     : https://prove2.me/submissions/5a671abb-6663-4a98-8b4f-8f5f546092ab

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_sum_lintegral_Ioc_le
public import Theorems.Thm_Auto_aux_log_weight_conversion_Ioc
public import Theorems.Thm_Auto_aux_log_holder_lintegral
public import Theorems.Thm_Auto_aux_pairwise_square_rpow_le_lintegral

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by
  let u : Fin (J + 1) → ℝ := fun j ↦ t j
  have hu : Monotone u := by
    intro i j hij
    exact ht hij
  let g : ℝ → ℝ≥0∞ := fun z ↦ ‖a z‖ₑ * ‖z * deriv a z‖ₑ
  have hsub (j : Fin J) : Set.Ioc (u j.castSucc) (u j.succ) ⊆ Set.Icc α β := by
    intro z hz
    exact ⟨(t j.castSucc).property.1.trans hz.1.le,
      hz.2.trans (t j.succ).property.2⟩
  have hpair (j : Fin J) :
      ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β := by
    have h := aux_pairwise_square_rpow_le_lintegral a ha
      (t j.castSucc).property (t j.succ).property (ht (Fin.castSucc_le_succ j))
    rw [aux_log_weight_conversion_Ioc
      (lt_of_lt_of_le hα (t j.castSucc).property.1) (hsub j) a (deriv a)] at h
    simpa only [u, g, ← enorm_eq_nnnorm] using h
  calc
    (∑ j : Fin J,
        ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤
        ∑ j : Fin J, 8 * ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β := Finset.sum_le_sum (fun j _ ↦ hpair j)
    _ = 8 * (∑ j : Fin J, ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β) := by rw [Finset.mul_sum]
    _ ≤ 8 * ∫⁻ z in Set.Icc α β, g z ∂aux_logarithmicMeasure α β := by
      gcongr
      exact aux_sum_lintegral_Ioc_le u hu g (t 0).property.1
        (t (Fin.last J)).property.2
    _ ≤ 8 * (aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z)) := by
      gcongr
      calc
        (∫⁻ z in Set.Icc α β, g z ∂aux_logarithmicMeasure α β) ≤
            ∫⁻ z, g z ∂aux_logarithmicMeasure α β := by
          exact lintegral_mono' Measure.restrict_le_self le_rfl
        _ ≤ _ := by
          simpa only [g] using aux_log_holder_lintegral a ha
    _ = 8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by ring
end Auto
