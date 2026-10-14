-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Perron
-- name    : dusart_psi_433_20261014_Perron
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:05.758367+00:00
-- url     : https://prove2.me/theorems/db05f84d-7075-4d83-8190-9387df32eaa4
-- title:
--   Dusart smoothing: Perron
-- statement:
--   This module gives the complete perron component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_MellinInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section
namespace DusartSmoothing

lemma continuous_quadratic_mellin_vertical (x σ : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => mellin (quadraticPrimeWeight x) (σ + t * I)) := by
  have hden : ∀ t : ℝ,
      (σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2) ≠ (0 : ℂ) := by
    intro t
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity) (quadratic_denominator_vertical_bound σ t hσ)
  have heq : (fun t : ℝ => mellin (quadraticPrimeWeight x) (σ + t * I)) =
      (fun t : ℝ => (x : ℂ) ^ (σ + t * I + 2) /
        ((σ + t * I) * (σ + t * I + 1) * (σ + t * I + 2))) := by
    funext t
    exact mellin_quadraticPrimeWeight x hx _ (by simpa using hσ)
  rw [heq]
  simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  fun_prop

lemma continuous_LSeries_term_vertical (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term f (σ + t * I) n) := by
  by_cases hn : n = 0
  · subst n; simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · simp_rw [LSeries.term_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn : (n : ℂ) ≠ 0)]
    exact continuous_const.div₀ (by fun_prop) (fun t => Complex.exp_ne_zero _)

lemma norm_LSeries_term_vertical (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term f (σ + t * I) n‖ = ‖LSeries.term f σ n‖ := by
  simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
    zero_mul, sub_self, add_zero]

lemma integrable_quadratic_mellin_mul_term (x σ : ℝ) (hx : 0 < x) (hσ : 0 < σ)
    (f : ℕ → ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => mellin (quadraticPrimeWeight x) (σ + t * I) *
      LSeries.term f (σ + t * I) n) := by
  have hMF := quadratic_mellin_verticalIntegrable x σ hx hσ
  have hmajor := hMF.norm.mul_const ‖LSeries.term f σ n‖
  apply hmajor.mono'
    ((continuous_quadratic_mellin_vertical x σ hx hσ).mul
      (continuous_LSeries_term_vertical f σ n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_LSeries_term_vertical])

lemma quadratic_mellin_prime_term_integral (x σ : ℝ) (hx : 0 < x) (hσ : 0 < σ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, mellin (quadraticPrimeWeight x) (σ + t * I) *
        LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + t * I) n) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * quadraticPrimeWeight x n := by
  by_cases hn : n = 0
  · subst n; simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := mellinInv_mellin_eq σ (quadraticPrimeWeight x) hnpos
    (quadraticPrimeWeight_mellinConvergent x hx.le σ (by simpa using hσ))
    (quadratic_mellin_verticalIntegrable x σ hx hσ)
    (quadraticPrimeWeight_continuousAt x n hnpos)
  rw [mellinInv] at h
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_natCast] at h
  have hC : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by push_cast; rfl
  rw [hC] at h
  have heq : (fun t : ℝ => mellin (quadraticPrimeWeight x) (σ + t * I) *
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + t * I) n) =
      (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((n : ℂ) ^ (-(σ + t * I)) * mellin (quadraticPrimeWeight x) (σ + t * I))) := by
    funext t
    rw [LSeries.term_def₀ (by simp)]
    ring
  rw [heq, integral_const_mul]
  calc (1 / (2 * Real.pi) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
      ∫ t : ℝ, (n : ℂ) ^ (-(σ + t * I)) * mellin (quadraticPrimeWeight x) (σ + t * I))
      = (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (n : ℂ) ^ (-(σ + t * I)) *
          mellin (quadraticPrimeWeight x) (σ + t * I)) := by ring
    _ = _ := by rw [h]

/-- The exact Perron integral for the actual integrated von Mangoldt sum. -/
theorem secondPsiPrimitive_perron (N : ℕ) (x σ : ℝ)
    (hx : 0 < x) (hN : x ≤ N) (hσ : 1 < σ) :
    (secondPsiPrimitive N x : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        mellin (quadraticPrimeWeight x) (σ + t * I) *
          (-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let F : ℕ → ℝ → ℂ := fun n t =>
    mellin (quadraticPrimeWeight x) (σ + t * I) * LSeries.term f (σ + t * I) n
  have hσpos : 0 < σ := by linarith
  have hMF := quadratic_mellin_verticalIntegrable x σ hx hσpos
  have hF : ∀ n : ℕ, Integrable (F n) :=
    fun n => integrable_quadratic_mellin_mul_term x σ hx hσpos f n
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (σ : ℂ)) (by simpa using hσ)).norm
    have heq : (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) =
        (fun n : ℕ => ‖LSeries.term f σ n‖ * ∫ t : ℝ,
          ‖mellin (quadraticPrimeWeight x) (σ + t * I)‖) := by
      funext n
      simp only [F, norm_mul, norm_LSeries_term_vertical]
      rw [integral_mul_const, mul_comm]
    rw [heq]
    exact hs.mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hF hsum
  have hseries : ∀ t : ℝ, (∑' n : ℕ, F n t) =
      mellin (quadraticPrimeWeight x) (σ + t * I) *
        (-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)) := by
    intro t
    simp only [F, tsum_mul_left]
    change mellin (quadraticPrimeWeight x) (σ + t * I) * LSeries f (σ + t * I) = _
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)]
  have hweight : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      quadraticPrimeWeight x n) = (secondPsiPrimitive N x : ℂ) := by
    rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
    · exact quadraticPrimeWeight_primeSum N x
    · intro n hn
      by_cases hn0 : n = 0
      · subst n; simp
      · have hNn : N < n := by
          simp only [Finset.mem_Ioc, not_and] at hn
          exact Nat.lt_of_not_ge (hn (Nat.pos_of_ne_zero hn0))
        have hxn : x < (n : ℝ) := hN.trans_lt (by exact_mod_cast hNn)
        rw [quadraticPrimeWeight, indicator_of_notMem
          (show (n : ℝ) ∉ Ioc 0 x from fun h => (not_le.mpr hxn) h.2)]
        simp
  rw [← hweight]
  calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * quadraticPrimeWeight x n)
      = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F n t := by
        apply tsum_congr
        intro n
        exact (quadratic_mellin_prime_term_integral x σ hx hσpos n).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, F n t := by
      rw [tsum_mul_left, hswap]
    _ = _ := by simp_rw [hseries]

end DusartSmoothing


