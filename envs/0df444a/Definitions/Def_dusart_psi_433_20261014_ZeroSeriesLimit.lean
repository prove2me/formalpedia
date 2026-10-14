-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroSeriesLimit
-- name    : dusart_psi_433_20261014_ZeroSeriesLimit
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:40:54.075979+00:00
-- url     : https://prove2.me/theorems/95750c8f-d59c-4cef-a5c8-3fba8eeed210
-- title:
--   Dusart smoothing: Zero Series Limit
-- statement:
--   This module gives the complete zero series limit component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
import Definitions.Def_dusart_psi_433_20261014_FinitePerron
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section
namespace DusartSmoothing
open Complex Set Topology Filter

noncomputable def truncatedZeros (T : ℝ) : Finset NontrivialZetaZero :=
  ((RvM.finite_symmetric_zero_window T).preimage Subtype.val_injective.injOn).toFinset

lemma mem_truncatedZeros (T : ℝ) (ρ : NontrivialZetaZero) :
    ρ ∈ truncatedZeros T ↔ |ρ.val.im| ≤ T := by
  simp [truncatedZeros, ρ.property]

lemma truncatedZeros_cofinal {α : Type*} {l : Filter α} {R : α → ℝ}
    (hR : Tendsto R l atTop) : Tendsto (fun j => truncatedZeros (R j)) l atTop := by
  simp only [Filter.atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro ρ
  filter_upwards [hR.eventually (eventually_ge_atTop |ρ.val.im|)] with j hj
  exact Finset.singleton_subset_iff.mpr ((mem_truncatedZeros (R j) ρ).2 hj)

lemma truncatedZeros_image (T : ℝ) :
    (truncatedZeros T).image (fun ρ : NontrivialZetaZero => ρ.val) =
      (RvM.finite_symmetric_zero_window T).toFinset := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp h
    rw [Set.Finite.mem_toFinset]
    exact ⟨τ.property, (mem_truncatedZeros T τ).1 hτ⟩
  · intro h
    rw [Set.Finite.mem_toFinset] at h
    exact Finset.mem_image.mpr ⟨⟨ρ, h.1⟩, (mem_truncatedZeros T ⟨ρ, h.1⟩).2 h.2, rfl⟩

lemma actual_quadratic_zero_window_sum_tendsto (x : ℝ) (hx : 1 ≤ x)
    {α : Type*} {l : Filter α} {R : α → ℝ} (hR : Tendsto R l atTop) :
    Tendsto (fun j => ∑ ρ ∈ (RvM.finite_symmetric_zero_window (R j)).toFinset,
        (RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ) l
      (𝓝 (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val)) := by
  have h := (actual_quadratic_zero_series_summable x hx).hasSum.comp (truncatedZeros_cofinal hR)
  have he : (fun j => ∑ ρ ∈ (RvM.finite_symmetric_zero_window (R j)).toFinset,
      (RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ) =
      (fun j => ∑ ρ ∈ truncatedZeros (R j), (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val) := by
    funext j
    rw [← truncatedZeros_image]
    exact Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)
  rw [he]
  exact h

end DusartSmoothing


