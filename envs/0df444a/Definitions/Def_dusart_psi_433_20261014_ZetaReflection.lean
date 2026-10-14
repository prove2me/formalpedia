-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaReflection
-- name    : dusart_psi_433_20261014_ZetaReflection
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:48:51.791545+00:00
-- url     : https://prove2.me/theorems/f24bf315-8cfd-4c15-9d88-ae3370fe0f2d
-- title:
--   Dusart smoothing: Zeta Reflection
-- statement:
--   This module gives the complete zeta reflection component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GammaStrip
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real

lemma gammaR_ne_zero_of_im_ne_zero {s : ℂ} (hi : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
  apply hi
  have hh := congrArg Complex.im hn
  simpa using hh

lemma gamma_half_not_neg_nat_of_im_ne_zero {s : ℂ} (hi : s.im ≠ 0) :
    ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m hm
  have hh := congrArg Complex.im hm
  norm_num at hh
  apply hi
  linarith

lemma logDeriv_zeta_reflection {s : ℂ} (hi : s.im ≠ 0)
    (hz : riemannZeta s ≠ 0) (hr : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s = -logDeriv riemannZeta (1 - s) -
      logDeriv Gammaℝ s - logDeriv Gammaℝ (1 - s) := by
  have h0 : s ≠ 0 := fun h => hi (by simp [h])
  have h1 : s ≠ 1 := fun h => hi (by simp [h])
  have hri : (1 - s).im ≠ 0 := by simpa using hi
  have hr0 : 1 - s ≠ 0 := fun h => hri (by simp [h])
  have hr1 : 1 - s ≠ 1 := fun h => hri (by simp [h])
  have hl := logDeriv_completedZeta_general h0 h1 hz
    (gammaR_ne_zero_of_im_ne_zero hi) (gamma_half_not_neg_nat_of_im_ne_zero hi)
  have hr' := logDeriv_completedZeta_general hr0 hr1 hr
    (gammaR_ne_zero_of_im_ne_zero hri) (gamma_half_not_neg_nat_of_im_ne_zero hri)
  have hf := logDeriv_completedZeta_one_sub s h0 h1
  linear_combination -hl - hr' + hf

lemma norm_logDeriv_zeta_conj (s : ℂ) :
    ‖logDeriv riemannZeta (starRingEnd ℂ s)‖ = ‖logDeriv riemannZeta s‖ := by
  rw [logDerivZeta_conj']
  simp

end DusartSmoothing.RvM


