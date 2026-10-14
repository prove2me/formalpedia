-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LowCutoff
-- name    : dusart_psi_433_20261014_LowCutoff
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:27:47.162481+00:00
-- url     : https://prove2.me/theorems/382870d0-3cf4-406b-8997-de930f66b210
-- title:
--   Dusart smoothing: Low Cutoff
-- statement:
--   This module gives the complete low cutoff component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LowHeightSharp
noncomputable section
namespace DusartSmoothing.LowHeight
open Complex Real Set MeasureTheory

lemma strip_norm_product_lt_forty (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht0 : 0 ≤ s.im) (htπ : s.im ≤ 2 * Real.pi) : ‖s * (1 - s)‖ < 40 := by
  by_cases ht : s.im < 1
  · have hn1 : ‖s‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg hσ0, abs_of_nonneg ht0] at h
      linarith
    have hn2 : ‖1 - s‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im (1 - s)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        zero_sub, abs_neg] at h
      rw [abs_of_nonneg (sub_nonneg.mpr hσ1), abs_of_nonneg ht0] at h
      linarith
    rw [norm_mul]
    nlinarith [norm_nonneg s, norm_nonneg (1 - s)]
  · have ht1 : 1 ≤ s.im := le_of_not_gt ht
    have ht2 : 1 ≤ s.im ^ 2 := by nlinarith
    have hp0 : 0 ≤ s.re * (1 - s.re) := mul_nonneg hσ0 (sub_nonneg.mpr hσ1)
    have hp1 : s.re * (1 - s.re) ≤ 1 / 4 := by nlinarith [sq_nonneg (s.re - 1 / 2)]
    have hd : 0 ≤ 2 * s.im ^ 2 - s.re * (1 - s.re) := by linarith
    have hprod := mul_nonneg hp0 hd
    have he : ‖s * (1 - s)‖ ^ 2 =
        (s.re ^ 2 + s.im ^ 2) * ((1 - s.re)^2 + s.im ^ 2) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
      simp [Complex.normSq, pow_two]
    have hn : ‖s * (1 - s)‖ ≤ s.im ^ 2 + 1 / 2 := by
      have hs : ‖s * (1 - s)‖ ^ 2 ≤ (s.im ^ 2 + 1 / 2)^2 := by
        rw [he]
        nlinarith [hprod]
      nlinarith [norm_nonneg (s * (1 - s))]
    have hπ : Real.pi < (3927 / 1250 : ℝ) := by have h := Real.pi_lt_d4; norm_num at h; exact h
    have htupper : s.im ^ 2 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos]

theorem zeta_nonzero_to_two_pi (s : ℂ) (hσ0 : 0 < s.re) (hσ1 : s.re < 1)
    (ht0 : 0 ≤ s.im) (htπ : s.im ≤ 2 * Real.pi) : riemannZeta s ≠ 0 := by
  have hs : s ≠ 0 := by intro h; subst s; simp at hσ0
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have hi := congrArg Complex.re h
    simp at hi
    linarith
  intro hz
  have hzC : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs] at hz
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · exact (Complex.Gammaℝ_ne_zero_of_re_pos hσ0 h).elim
  have hid : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [hzC] at h
    linear_combination -h
  have he : s * (1 - s) * completedRiemannZeta₀ s = 1 := by
    rw [hid]
    field_simp
    ring
  have hsmall := completed_entire_sharp s hσ0.le hσ1.le
  have hnprod := strip_norm_product_lt_forty s hσ0.le hσ1.le ht0 htπ
  have hn : ‖s * (1 - s) * completedRiemannZeta₀ s‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (s * (1 - s)), norm_nonneg (completedRiemannZeta₀ s)]
  rw [he] at hn
  norm_num at hn


theorem nontrivial_zero_height_gt_two_pi (s : ℂ)
    (hzero : riemannZeta s = 0) (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    2 * Real.pi < |s.im| := by
  by_contra h
  have hsmall : |s.im| ≤ 2 * Real.pi := le_of_not_gt h
  rcases le_total 0 s.im with ht | ht
  · exact zeta_nonzero_to_two_pi s hσ0 hσ1 ht ((le_abs_self _).trans hsmall) hzero
  · have hn := zeta_nonzero_to_two_pi (starRingEnd ℂ s) (by simpa using hσ0)
      (by simpa using hσ1) (by simpa using neg_nonneg.mpr ht)
      (by simpa using (neg_le_abs s.im).trans hsmall)
    apply hn
    rw [riemannZeta_conj, hzero, map_zero]

end DusartSmoothing.LowHeight


