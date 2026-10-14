-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronLeftLine
-- name    : dusart_psi_433_20261014_PerronLeftLine
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:47:48.348677+00:00
-- url     : https://prove2.me/theorems/675f995a-aeab-4925-9555-5ead4be04a49
-- title:
--   Dusart smoothing: Perron Left Line
-- statement:
--   This module gives the complete perron left line component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZetaLeftBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace DusartSmoothing
open Complex Real MeasureTheory Filter Topology

lemma perron_left_denominator_bounds (t : ℝ) :
    let s : ℂ := -(1 / 2) + t * I
    let d := ‖s‖ * ‖s + 1‖ * ‖s + 2‖
    (3 / 8 : ℝ) ≤ d ∧ |t| ^ 3 ≤ d := by
  dsimp
  let s : ℂ := -(1 / 2) + t * I
  have h0 : (1 / 2 : ℝ) ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    norm_num [s] at h
    exact h
  have h1 : (1 / 2 : ℝ) ≤ ‖s + 1‖ := by
    have h := Complex.abs_re_le_norm (s + 1)
    norm_num [s] at h
    exact h
  have h2 : (3 / 2 : ℝ) ≤ ‖s + 2‖ := by
    have h := Complex.abs_re_le_norm (s + 2)
    norm_num [s] at h
    exact h
  have ht0 : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have ht1 : |t| ≤ ‖s + 1‖ := by simpa [s] using Complex.abs_im_le_norm (s + 1)
  have ht2 : |t| ≤ ‖s + 2‖ := by simpa [s] using Complex.abs_im_le_norm (s + 2)
  constructor
  · change 3 / 8 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖
    calc (3 / 8 : ℝ) = (1 / 2) * (1 / 2) * (3 / 2) := by norm_num
      _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by gcongr
  · change |t| ^ 3 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖
    calc |t| ^ 3 = |t| * |t| * |t| := by ring
      _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by gcongr

lemma linear_over_cubic_bound (u d : ℝ) (hu : 0 ≤ u)
    (hd : (3 / 8 : ℝ) ≤ d) (hc : u ^ 3 ≤ d) :
    (u + 32) * (1 + u ^ 2) ≤ 256 * d := by
  by_cases h : u ≤ 1
  · have h1 : u + 32 ≤ 33 := by linarith
    have h2 : 1 + u ^ 2 ≤ 2 := by nlinarith
    have hm := mul_le_mul h1 h2 (by positivity) (by norm_num : (0 : ℝ) ≤ 33)
    nlinarith
  · have hu1 : 1 ≤ u := le_of_not_ge h
    have h1 : u + 32 ≤ 33 * u := by linarith
    have h2 : 1 + u ^ 2 ≤ 2 * u ^ 2 := by nlinarith
    have hm := mul_le_mul h1 h2 (by positivity) (by positivity : 0 ≤ 33 * u)
    nlinarith

lemma norm_perron_left_majorant (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖perronIntegrand x (-(1 / 2 : ℂ) + t * I)‖ ≤
      256 * x ^ (3 / 2 : ℝ) / (1 + t ^ 2) := by
  let s : ℂ := -(1 / 2) + t * I
  let d : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖
  have hb := perron_left_denominator_bounds t
  change 3 / 8 ≤ d ∧ |t| ^ 3 ≤ d at hb
  have hd : 0 < d := by linarith [hb.1]
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hK : ‖quadraticKernel x s‖ = x ^ (3 / 2 : ℝ) / d := by
    rw [quadraticKernel, norm_div, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    norm_num [s, d]
  have hZ := RvM.norm_logDeriv_zeta_left t
  change ‖logDeriv riemannZeta s‖ ≤ |t| + 32 at hZ
  have hl := linear_over_cubic_bound |t| d (abs_nonneg _) hb.1 hb.2
  rw [sq_abs] at hl
  change ‖-quadraticKernel x s * logDeriv riemannZeta s‖ ≤ _
  rw [norm_mul, norm_neg, hK]
  calc x ^ (3 / 2 : ℝ) / d * ‖logDeriv riemannZeta s‖
      ≤ x ^ (3 / 2 : ℝ) / d * (|t| + 32) := by gcongr
    _ ≤ 256 * x ^ (3 / 2 : ℝ) / (1 + t ^ 2) := by
      apply (le_div_iff₀ ht).2
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (div_le_iff₀ hd).2
      nlinarith [mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hx.le (3 / 2 : ℝ))]

lemma continuous_perron_left (x : ℝ) (hx : 0 < x) :
    Continuous (fun t : ℝ => perronIntegrand x (-(1 / 2 : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h0 : -(1 / 2 : ℂ) + t * I ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh
  have h1 : -(1 / 2 : ℂ) + t * I ≠ 1 := by
    intro h; have hh := congrArg Complex.re h; norm_num at hh
  have hZ := zeta_nonzero_left_half_strip (-(1 / 2 : ℂ) + t * I)
    (by norm_num) (by norm_num)
  exact (perronIntegrand_analyticAt x hx _ (by norm_num) h0 h1 hZ).continuousAt.comp
    (f := fun t : ℝ => -(1 / 2 : ℂ) + t * I) (by fun_prop)

lemma perron_left_vertical_integrable (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => perronIntegrand x (-(1 / 2 : ℂ) + t * I)) := by
  apply (integrable_inv_one_add_sq.const_mul (256 * x ^ (3 / 2 : ℝ))).mono'
    (continuous_perron_left x hx).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Pi.mul_apply, div_eq_mul_inv] using norm_perron_left_majorant x hx t

lemma norm_perron_left_integral (x : ℝ) (hx : 0 < x) :
    ‖∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I)‖ ≤
      256 * Real.pi * x ^ (3 / 2 : ℝ) := by
  calc _ ≤ ∫ t : ℝ, ‖perronIntegrand x (-(1 / 2 : ℂ) + t * I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, 256 * x ^ (3 / 2 : ℝ) * (1 + t ^ 2)⁻¹ := by
      apply integral_mono (perron_left_vertical_integrable x hx).norm
        (integrable_inv_one_add_sq.const_mul _)
      intro t
      simpa only [div_eq_mul_inv] using norm_perron_left_majorant x hx t
    _ = 256 * Real.pi * x ^ (3 / 2 : ℝ) := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      ring

lemma perron_left_vertical_tendsto (x : ℝ) (hx : 0 < x) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun j => ∫ t in -R j..R j, perronIntegrand x (-(1 / 2 : ℂ) + t * I))
      atTop (𝓝 (∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I))) := by
  exact intervalIntegral_tendsto_integral (perron_left_vertical_integrable x hx)
    (Filter.tendsto_neg_atTop_atBot.comp hR) hR

end DusartSmoothing


