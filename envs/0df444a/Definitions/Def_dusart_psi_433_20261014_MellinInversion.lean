-- Prove2me | Definitions.Def_dusart_psi_433_20261014_MellinInversion
-- name    : dusart_psi_433_20261014_MellinInversion
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:02.269119+00:00
-- url     : https://prove2.me/theorems/5ea6f11d-0b8a-4327-8934-fa366fb912dd
-- title:
--   Dusart smoothing: Mellin Inversion
-- statement:
--   This module gives the complete mellin inversion component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Mellin
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex Set MeasureTheory Filter
open scoped Topology

namespace DusartSmoothing

lemma quadratic_denominator_vertical_bound (σ t : ℝ) (hσ : 0 < σ) :
    σ * (1 + t ^ 2) ≤
      ‖(σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2)‖ := by
  let s : ℂ := σ + t * I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have h0 : σ ≤ ‖s‖ := hre ▸ Complex.re_le_norm s
  have h1 : 1 + t ^ 2 ≤ ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero, hre, him]
    nlinarith
  have h2 : 1 + t ^ 2 ≤ ‖s + 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.re_ofNat, Complex.add_im, Complex.im_ofNat,
      add_zero, hre, him]
    nlinarith
  have hq : 0 ≤ 1 + t ^ 2 := by positivity
  have hn1 : Real.sqrt (1 + t ^ 2) ≤ ‖s + 1‖ := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (1 + t ^ 2), norm_nonneg (s + 1)]
  have hn2 : Real.sqrt (1 + t ^ 2) ≤ ‖s + 2‖ := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (1 + t ^ 2), norm_nonneg (s + 2)]
  have h12 : 1 + t ^ 2 ≤ ‖s + 1‖ * ‖s + 2‖ := by
    have hh := mul_le_mul hn1 hn2 (Real.sqrt_nonneg _) (norm_nonneg _)
    simpa only [← pow_two, Real.sq_sqrt hq] using hh
  have hh := mul_le_mul h0 h12 hq (norm_nonneg s)
  simpa only [norm_mul, mul_assoc] using hh

lemma norm_quadratic_mellin_vertical_le (x σ t : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    ‖mellin (quadraticPrimeWeight x) (σ + t * I)‖ ≤
      (x ^ (σ + 2) / σ) * (1 + t ^ 2)⁻¹ := by
  have hs : 0 < (σ + t * I : ℂ).re := by simpa using hσ
  rw [mellin_quadraticPrimeWeight x hx _ hs, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero,
    Complex.re_ofNat]
  calc x ^ (σ + 2) / ‖(σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2)‖
      ≤ x ^ (σ + 2) / (σ * (1 + t ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (quadratic_denominator_vertical_bound σ t hσ)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

lemma quadratic_mellin_verticalIntegrable (x σ : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    VerticalIntegrable (mellin (quadraticPrimeWeight x)) σ := by
  have hden : ∀ t : ℝ,
      (σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2) ≠ (0 : ℂ) := by
    intro t
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity) (quadratic_denominator_vertical_bound σ t hσ)
  have hcont : Continuous (fun t : ℝ =>
      (x : ℂ) ^ (σ + t * I + 2) /
        ((σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2))) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    fun_prop
  have heq : (fun t : ℝ => mellin (quadraticPrimeWeight x) (σ + t * I)) =
      (fun t : ℝ => (x : ℂ) ^ (σ + t * I + 2) /
        ((σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2))) := by
    funext t
    exact mellin_quadraticPrimeWeight x hx _ (by simpa using hσ)
  unfold VerticalIntegrable
  have hmajor : Integrable (fun t : ℝ => (x ^ (σ + 2) / σ) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hmajor.mono' (heq ▸ hcont.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => norm_quadratic_mellin_vertical_le x σ t hx hσ)

lemma quadraticPrimeWeight_eq_positivePart (x t : ℝ) (ht : 0 < t) :
    quadraticPrimeWeight x t = ((max (x - t) 0 : ℝ) : ℂ) ^ 2 / 2 := by
  by_cases htx : t ≤ x
  · rw [quadraticPrimeWeight, indicator_of_mem (show t ∈ Ioc 0 x from ⟨ht, htx⟩),
      max_eq_left (by linarith : 0 ≤ x - t)]
    push_cast
    rfl
  · rw [quadraticPrimeWeight, indicator_of_notMem (show t ∉ Ioc 0 x from fun h => htx h.2),
      max_eq_right (by linarith : x - t ≤ 0)]
    simp

lemma quadraticPrimeWeight_continuousAt (x y : ℝ) (hy : 0 < y) :
    ContinuousAt (quadraticPrimeWeight x) y := by
  have hcont : ContinuousAt (fun t : ℝ => ((max (x - t) 0 : ℝ) : ℂ) ^ 2 / 2) y := by
    fun_prop
  apply hcont.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with t ht
  exact quadraticPrimeWeight_eq_positivePart x t ht

theorem mellinInv_quadraticPrimeWeight (x σ y : ℝ)
    (hx : 0 < x) (hσ : 0 < σ) (hy : 0 < y) :
    mellinInv σ (fun s : ℂ => (x : ℂ) ^ (s + 2) / (s * (s + 1) * (s + 2))) y =
      ((max (x - y) 0 : ℝ) : ℂ) ^ 2 / 2 := by
  have h := mellinInv_mellin_eq σ (quadraticPrimeWeight x) hy
    (quadraticPrimeWeight_mellinConvergent x hx.le σ (by simpa using hσ))
    (quadratic_mellin_verticalIntegrable x σ hx hσ)
    (quadraticPrimeWeight_continuousAt x y hy)
  rw [quadraticPrimeWeight_eq_positivePart x y hy] at h
  rw [mellinInv] at h ⊢
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mellin_quadraticPrimeWeight x hx _ (by simpa using hσ)]

end DusartSmoothing


