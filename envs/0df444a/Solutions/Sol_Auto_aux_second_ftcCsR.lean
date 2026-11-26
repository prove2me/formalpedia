-- Prove2me | solution 1 for Auto.aux_second_ftcCsR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:50.08991+00:00
-- url     : https://prove2.me/submissions/5ce34154-37b7-4ad0-863b-f628e01e1906

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_chain_second_energy_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  let R : ℝ≥0∞ := 8 * aux_logarithmicL2 α β a *
    aux_logarithmicL2 α β (fun t ↦ t * deriv a t)
  have hchain (t : {u : Fin (J + 1) → Set.Icc α β // Monotone u}) :
      (∑ j : Fin J,
        ((‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤ R := by
    simpa only [R] using aux_chain_second_energy_le hα a ha t.1 t.2
  have hroot (t : {u : Fin (J + 1) → Set.Icc α β // Monotone u}) :
      (∑ j : Fin J,
        ((‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ^
          ((2 : ℝ)⁻¹) ≤ R ^ ((2 : ℝ)⁻¹) :=
    ENNReal.rpow_le_rpow (hchain t) (by norm_num)
  have hsup : finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J ≤
      R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro t
    exact hroot t
  calc
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
        (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hsup (by norm_num)
    _ = R := by
      rw [← ENNReal.rpow_mul]
      norm_num
    _ = 8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rfl
end Auto
