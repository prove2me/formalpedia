-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaStrip
-- name    : dusart_psi_433_20261014_GammaStrip
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:47:40.931162+00:00
-- url     : https://prove2.me/theorems/015ffa86-2abd-4cea-8597-59b1a791073b
-- title:
--   Dusart smoothing: Gamma Strip
-- statement:
--   This module gives the complete gamma strip component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZetaLeftBound
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real

lemma integerComplement_of_im_ne_zero {w : ℂ} (hi : w.im ≠ 0) :
    w ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h := congrArg Complex.im hn
  simp at h
  exact hi h.symm

lemma norm_digamma_strip {w : ℂ} (hlo : -(1 / 4 : ℝ) ≤ w.re) (hu : w.re ≤ 1)
    (hi : 1 ≤ |w.im|) : ‖digamma w‖ ≤ 2 * |w.im| + 7 := by
  have him : w.im ≠ 0 := by intro h; rw [h, abs_zero] at hi; norm_num at hi
  have hs : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hm
    apply him
    have h := congrArg Complex.im hm
    simpa using h
  have hwp : 0 < (w + 1).re := by simp; linarith
  have hwm : (w + 1).im ≠ 0 := by simpa using him
  have hn : ‖w + 1‖ ≤ 2 + |w.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (w + 1)
    rw [abs_of_pos hwp] at h
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at h
    linarith
  have hw1 : 1 ≤ ‖w‖ := hi.trans (Complex.abs_im_le_norm w)
  have hv1 : 1 ≤ ‖w + 1‖ := by
    have h := Complex.abs_im_le_norm (w + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero] at h
    exact hi.trans h
  have hiw : ‖w⁻¹‖ ≤ (1 : ℝ) := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hw1
  have hiv : ‖1 / (w + 1)‖ ≤ (1 : ℝ) := by
    rw [one_div, norm_inv]
    exact inv_le_one_of_one_le₀ hv1
  have hψ := norm_digamma_linear hwp (integerComplement_of_im_ne_zero hwm)
  have hr := digamma_apply_add_one w hs
  have he : digamma w = digamma (w + 1) - w⁻¹ := by linear_combination -hr
  rw [he]
  have hb := norm_sub_le (digamma (w + 1)) w⁻¹
  nlinarith

lemma norm_logDeriv_GammaR_strip {s : ℂ} (hlo : -(1 / 2 : ℝ) ≤ s.re)
    (hu : s.re ≤ 2) (hi : 2 ≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤ |s.im| / 2 + 5 := by
  have hsi : (s / 2).im ≠ 0 := by
    have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at hi; norm_num at hi
    simpa using him
  have hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    apply hsi
    have h := congrArg Complex.im hm
    simpa using h
  have hwlo : -(1 / 4 : ℝ) ≤ (s / 2).re := by norm_num; linarith
  have hwu : (s / 2).re ≤ 1 := by norm_num; linarith
  have hwi : 1 ≤ |(s / 2).im| := by norm_num [abs_div]; linarith
  have hp := norm_digamma_strip hwlo hwu hwi
  norm_num [abs_div] at hp
  rw [logDeriv_GammaR_general hs]
  have hn := norm_add_le (-(Real.log Real.pi : ℂ) / 2) ((1 / 2 : ℂ) * digamma (s / 2))
  norm_num [norm_mul, norm_div] at hn
  linarith [abs_log_pi_le_three]

end DusartSmoothing.RvM


