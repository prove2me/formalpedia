-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronRightLine
-- name    : dusart_psi_433_20261014_PerronRightLine
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:41:46.520386+00:00
-- url     : https://prove2.me/theorems/92d6eaf0-ef48-4461-a28a-befa2169f60b
-- title:
--   Dusart smoothing: Perron Right Line
-- statement:
--   This module gives the complete perron right line component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroSeriesLimit
noncomputable section
namespace DusartSmoothing
open Complex Set MeasureTheory Filter Topology

lemma perron_right_vertical_integrable (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => perronIntegrand x (2 + t * I)) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let M : ℝ := ∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖
  have hbound : ∀ t : ℝ, ‖logDeriv riemannZeta (2 + t * I)‖ ≤ M := by
    intro t
    have hs : LSeriesSummable f (2 + t * I) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
    have he : LSeries f (2 + t * I) = -logDeriv riemannZeta (2 + t * I) := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by norm_num)]
      simp only [logDeriv_apply, neg_div]
    have h := norm_tsum_le_tsum_norm hs.norm
    rw [show (∑' n : ℕ, LSeries.term f (2 + t * I) n) = LSeries f (2 + t * I) from rfl,
      he, norm_neg] at h
    have hterm : ∀ n : ℕ, ‖LSeries.term f (2 + t * I) n‖ = ‖LSeries.term f (2 : ℂ) n‖ := by
      intro n
      simpa only [Complex.ofReal_ofNat] using norm_LSeries_term_vertical f 2 t n
    simp_rw [hterm] at h
    exact h
  have hcZ : Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h1 : (2 : ℂ) + t * I ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num at hh
    have hz := riemannZeta_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 + t * I : ℂ).re)
    exact (RvM.continuousAt_logDeriv_zeta h1 hz).comp
      (f := fun t : ℝ => (2 : ℂ) + t * I) (by fun_prop)
  have he : (fun t : ℝ => perronIntegrand x (2 + t * I)) =
      (fun t : ℝ => -mellin (quadraticPrimeWeight x) (2 + t * I) *
        logDeriv riemannZeta (2 + t * I)) := by
    funext t
    rw [perronIntegrand, quadraticKernel_eq_mellin x hx _ (by norm_num)]
  rw [he]
  have hMF := quadratic_mellin_verticalIntegrable x 2 hx (by norm_num)
  apply (hMF.norm.mul_const M).mono'
    (((continuous_quadratic_mellin_vertical x 2 hx (by norm_num)).neg.mul hcZ).aestronglyMeasurable)
  filter_upwards [] with t
  simp only [Pi.mul_apply, Pi.neg_apply, Complex.ofReal_ofNat]
  rw [norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

lemma secondPsiPrimitive_perron_kernel (N : ℕ) (x : ℝ) (hx : 0 < x) (hN : x ≤ N) :
    (secondPsiPrimitive N x : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, perronIntegrand x (2 + t * I) := by
  rw [secondPsiPrimitive_perron N x 2 hx hN (by norm_num)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [perronIntegrand, quadraticKernel_eq_mellin x hx _ (by norm_num), logDeriv_apply]
  norm_num only [Complex.ofReal_ofNat]
  ring

lemma perron_right_vertical_tendsto (x : ℝ) (hx : 0 < x) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun j => ∫ t in -R j..R j, perronIntegrand x (2 + t * I)) atTop
      (𝓝 (∫ t : ℝ, perronIntegrand x (2 + t * I))) := by
  exact intervalIntegral_tendsto_integral (perron_right_vertical_integrable x hx)
    (Filter.tendsto_neg_atTop_atBot.comp hR) hR

end DusartSmoothing


