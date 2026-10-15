-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ResamplingNorm
-- name    : dusart_psi_433_20261014_ResamplingNorm
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T12:15:12.165563+00:00
-- url     : https://prove2.me/theorems/f093cc0d-ed2a-4392-86cb-f44d94cc04ba
-- title:
--   Dusart smoothing: Resampling Norm
-- statement:
--   This module gives the complete resampling norm component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PositiveResamplingNorm
noncomputable section
namespace DusartSmoothing
open Complex Set

lemma finite_resampling_norm_bound (R x ν a : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed (X R x) ≤ ν)
    (hk : k (X R x) ν = 1) (ha : 0 < a)
    (hab : a + 2 * (optimalWidth (X R x) ν * x) ≤ x * (1 + 2 * optimalWidth (X R x) ν))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ) :
    (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) ≤
      x * (1 + 2 * optimalWidth (X R x) ν)^3 * optimalWidth (X R x) ν := by
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
  have hB := finite_positive_resampling_norm_bound R x ν a hR hx hzero hX hν hν1 hseed hk ha hab C hC
  dsimp [C] at hB
  rw [Finset.sum_image (fun a _ b _ he => by
    have hh := congrArg (starRingEnd ℂ) he
    simpa using hh)] at hB
  have he : (∑ ρ ∈ Zn, ‖(RvM.zeroMult (starRingEnd ℂ ρ) : ℂ) *
      smoothedZeroKernel a (optimalWidth (X R x) ν * x) (starRingEnd ℂ ρ)‖) =
      ∑ ρ ∈ Zn, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hh := (hneg ρ hρ).1.2.2
    apply norm_weighted_smoothed_conj a (optimalWidth (X R x) ν * x) ha
      (mul_pos (optimalWidth_pos (X R x) ν (threshold_facts R x hR hX).1 hν) (by linarith)) ρ
    intro he
    rw [he] at hh
    norm_num at hh
  rw [he] at hB
  have hP := finite_positive_resampling_norm_bound R x ν a hR hx hzero hX hν hν1 hseed hk ha hab Zp hpos
  have hsplit : (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) =
      (∑ ρ ∈ Zp, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) +
      (∑ ρ ∈ Zn, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) := by
    exact (Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 < ρ.im) _).symm
  rw [hsplit]
  linarith

lemma resampling_zero_series_norm_bound (R x ν a : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed (X R x) ≤ ν)
    (hk : k (X R x) ν = 1) (ha : 1 ≤ a)
    (hab : a + 2 * (optimalWidth (X R x) ν * x) ≤ x * (1 + 2 * optimalWidth (X R x) ν)) :
    (∑' ρ : NontrivialZetaZero,
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ.val‖) ≤
        x * (1 + 2 * optimalWidth (X R x) ν)^3 * optimalWidth (X R x) ν := by
  classical
  have hh : 0 < optimalWidth (X R x) ν * x :=
    mul_pos (optimalWidth_pos (X R x) ν (threshold_facts R x hR hX).1 hν) (by linarith)
  apply (smoothed_zero_series_summable a (optimalWidth (X R x) ν * x) ha hh).norm.tsum_le_of_sum_le
  intro S
  let Z : Finset ℂ := S.image (fun ρ : NontrivialZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hρ
    exact he ▸ τ.property
  have hb := finite_resampling_norm_bound R x ν a hR hx hzero hX hν hν1 hseed hk
    (by linarith) hab Z hZ
  dsimp [Z] at hb
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hb
  exact hb

end DusartSmoothing


