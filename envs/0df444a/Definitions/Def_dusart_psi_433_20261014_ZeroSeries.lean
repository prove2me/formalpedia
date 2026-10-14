-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroSeries
-- name    : dusart_psi_433_20261014_ZeroSeries
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:39:39.108418+00:00
-- url     : https://prove2.me/theorems/18dd672b-e1d1-4ce2-87fe-2b227dd7f54b
-- title:
--   Dusart smoothing: Zero Series
-- statement:
--   This module gives the complete zero series component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroNormSums
import Definitions.Def_dusart_psi_433_20261014_PerronKernelConj
noncomputable section
namespace DusartSmoothing
open Complex Set

lemma finite_quadratic_zero_norm_sum_bound (x : ℝ) (hx : 1 ≤ x) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ) :
    (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖) ≤ 24 * x^3 := by
  classical
  let Zp := Z.filter (fun ρ => 0 < ρ.im)
  let Zn := Z.filter (fun ρ => ¬0 < ρ.im)
  have hpos : ∀ ρ ∈ Zp, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    exact ⟨hZ ρ hmem, hγ⟩
  have hneg : ∀ ρ ∈ Zn, RvM.IsNontrivialZero ρ ∧ ρ.im < 0 := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    have hnt := hZ ρ hmem
    have hn : ρ.im ≠ 0 := by
      intro he
      have hh := RvM.nontrivial_zero_abs_height ρ hnt
      rw [he, abs_zero] at hh
      linarith [Real.pi_pos]
    exact ⟨hnt, lt_of_le_of_ne (le_of_not_gt hγ) hn⟩
  let C := Zn.image (starRingEnd ℂ)
  have hC : ∀ ρ ∈ C, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hnt, him⟩ := hneg τ hτ
    refine ⟨⟨?_, by simpa using hnt.2.1, by simpa using hnt.2.2⟩, ?_⟩
    · rw [riemannZeta_conj, hnt.1, map_zero]
    · simpa using neg_pos.mpr him
  have hB := finite_positive_quadratic_norm_sum_bound x hx C hC
  dsimp [C] at hB
  rw [Finset.sum_image (fun a _ b _ he => by
    have hh := congrArg (starRingEnd ℂ) he
    simpa using hh)] at hB
  have he : (∑ ρ ∈ Zn, ‖(RvM.zeroMult (starRingEnd ℂ ρ) : ℂ) *
      quadraticKernel x (starRingEnd ℂ ρ)‖) =
      ∑ ρ ∈ Zn, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hh := (hneg ρ hρ).1.2.2
    apply norm_weighted_quadratic_conj x (by linarith) ρ
    intro he
    rw [he] at hh
    norm_num at hh
  rw [he] at hB
  have hP := finite_positive_quadratic_norm_sum_bound x hx Zp hpos
  have hsplit : (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖) =
      (∑ ρ ∈ Zp, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖) +
      (∑ ρ ∈ Zn, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖) := by
    exact (Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 < ρ.im) _).symm
  rw [hsplit]
  linarith

abbrev NontrivialZetaZero := {ρ : ℂ // RvM.IsNontrivialZero ρ}

lemma actual_quadratic_zero_series_absolutely_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun ρ : NontrivialZetaZero =>
      ‖(RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val‖) := by
  classical
  apply summable_of_sum_le (c := 24 * x^3) (fun ρ => norm_nonneg _)
  intro S
  let Z : Finset ℂ := S.image (fun ρ : NontrivialZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hρ
    exact he ▸ τ.property
  have h := finite_quadratic_zero_norm_sum_bound x hx Z hZ
  dsimp [Z] at h
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
  exact h

lemma actual_quadratic_zero_series_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun ρ : NontrivialZetaZero => (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val) :=
  (actual_quadratic_zero_series_absolutely_summable x hx).of_norm

end DusartSmoothing


