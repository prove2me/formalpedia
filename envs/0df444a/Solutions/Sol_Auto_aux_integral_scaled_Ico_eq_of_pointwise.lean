-- Prove2me | solution 1 for Auto.aux_integral_scaled_Ico_eq_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:01.34088+00:00
-- url     : https://prove2.me/submissions/7425184c-5f8b-48e9-a1a2-c0f3c7555550

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_integral_scaled_Ico_eq_setIntegral

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {N : ℕ}
    (P Q : ℝ → ℝ) (hPQ : ∀ s, s ∈ Ico (0 : ℝ) N → P s = Q s) :
    ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s) *
        P s =
      (N : ℝ)⁻¹ * ∫ s in Ico (0 : ℝ) N, Q s := by
  rw [aux_integral_scaled_Ico_eq_setIntegral]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
  exact hPQ s hs
end Auto
