-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Mellin
-- name    : dusart_psi_433_20261014_Mellin
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:25.987433+00:00
-- url     : https://prove2.me/theorems/ccb9364d-921c-4efd-a6d6-9ef2b0efcf2b
-- title:
--   Dusart smoothing: Mellin
-- statement:
--   This module gives the complete mellin component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_IntegratedPsi
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Complex intervalIntegral

namespace DusartSmoothing

lemma positive_real_part_ne_zero (s : ℂ) (hs : 0 < s.re) : s ≠ 0 := by
  intro he
  rw [he, Complex.zero_re] at hs
  exact lt_irrefl 0 hs

lemma integral_cpow_monomial (x : ℝ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1)) = (x : ℂ) ^ s / s := by
  have h := integral_cpow (a := 0) (b := x) (r := s - 1)
    (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))
  simpa only [sub_add_cancel, Complex.ofReal_zero,
    Complex.zero_cpow (positive_real_part_ne_zero s hs), sub_zero] using h

lemma cpow_add_one (z s : ℂ) (hz : z ≠ 0) : z ^ (s + 1) = z ^ s * z := by
  rw [Complex.cpow_add s 1 hz, Complex.cpow_one]

lemma cpow_add_two (z s : ℂ) (hz : z ≠ 0) : z ^ (s + 2) = z ^ s * z ^ 2 := by
  rw [Complex.cpow_add s 2 hz]
  norm_num

lemma quadratic_power_expansion (x t : ℝ) (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * ((x : ℂ) - t) ^ 2 / 2 =
      ((x : ℂ) ^ 2 * (t : ℂ) ^ (s - 1) -
        (2 * (x : ℂ)) * (t : ℂ) ^ s + (t : ℂ) ^ (s + 1)) / 2 := by
  have htn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have he₁ : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * (t : ℂ) := by
    calc
      _ = (t : ℂ) ^ ((s - 1) + 1) := by congr 1; ring
      _ = _ := cpow_add_one _ _ htn
  have he₂ : (t : ℂ) ^ (s + 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 2 := by
    calc
      _ = (t : ℂ) ^ ((s - 1) + 2) := by congr 1; ring
      _ = _ := cpow_add_two _ _ htn
  rw [he₁, he₂]
  ring

lemma quadratic_power_intervalIntegrable (x : ℝ) (hx : 0 ≤ x)
    (s : ℂ) (hs : 0 < s.re) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((x : ℂ) - t) ^ 2 / 2)
      volume 0 x := by
  have hi₀ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1)) volume 0 x :=
    intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hi₁ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ s) volume 0 x :=
    intervalIntegrable_cpow' (by linarith)
  have hi₂ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s + 1)) volume 0 x :=
    intervalIntegrable_cpow' (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hi := (((hi₀.const_mul ((x : ℂ) ^ 2)).sub (hi₁.const_mul (2 * (x : ℂ)))).add hi₂).div_const 2
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
  apply hi.1.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (quadratic_power_expansion x t s ht.1).symm

theorem integral_quadratic_power (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) * ((x : ℂ) - t) ^ 2 / 2) =
      (x : ℂ) ^ (s + 2) / (s * (s + 1) * (s + 2)) := by
  have hi₀ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1)) volume 0 x :=
    intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hi₁ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ s) volume 0 x :=
    intervalIntegrable_cpow' (by linarith)
  have hi₂ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s + 1)) volume 0 x :=
    intervalIntegrable_cpow' (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have he : (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) * ((x : ℂ) - t) ^ 2 / 2) =
      ∫ t in (0 : ℝ)..x, ((x : ℂ) ^ 2 * (t : ℂ) ^ (s - 1) -
        (2 * (x : ℂ)) * (t : ℂ) ^ s + (t : ℂ) ^ (s + 1)) / 2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le hx.le
    intro t ht
    exact quadratic_power_expansion x t s ht.1
  rw [he, intervalIntegral.integral_div]
  have he' : (∫ t in (0 : ℝ)..x, (x : ℂ) ^ 2 * (t : ℂ) ^ (s - 1) -
      (2 * (x : ℂ)) * (t : ℂ) ^ s + (t : ℂ) ^ (s + 1)) =
      (x : ℂ) ^ 2 * (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1)) -
        (2 * (x : ℂ)) * (∫ t in (0 : ℝ)..x, (t : ℂ) ^ s) +
          (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s + 1)) := by
    rw [intervalIntegral.integral_add
      ((hi₀.const_mul ((x : ℂ) ^ 2)).sub (hi₁.const_mul (2 * (x : ℂ)))) hi₂,
      intervalIntegral.integral_sub (hi₀.const_mul ((x : ℂ) ^ 2))
        (hi₁.const_mul (2 * (x : ℂ))), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [he']
  have hs₁ : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hs₂ : 0 < (s + 2).re := by simp only [Complex.add_re, Complex.re_ofNat]; linarith
  have h₀ := positive_real_part_ne_zero s hs
  have h₁ := positive_real_part_ne_zero (s + 1) hs₁
  have h₂ := positive_real_part_ne_zero (s + 2) hs₂
  have hxn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hi₁' : (∫ t in (0 : ℝ)..x, (t : ℂ) ^ s) = (x : ℂ) ^ (s + 1) / (s + 1) := by
    simpa using integral_cpow_monomial x (s + 1) hs₁
  have hi₂' : (∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s + 1)) = (x : ℂ) ^ (s + 2) / (s + 2) := by
    simpa only [show s + 2 - 1 = s + 1 by ring] using integral_cpow_monomial x (s + 2) hs₂
  rw [integral_cpow_monomial x s hs, hi₁', hi₂', cpow_add_one _ _ hxn,
    cpow_add_two _ _ hxn]
  field_simp
  ring

noncomputable def quadraticPrimeWeight (x : ℝ) : ℝ → ℂ :=
  (Ioc 0 x).indicator (fun t : ℝ => ((x : ℂ) - t) ^ 2 / 2)

lemma quadratic_mellin_integrand (x : ℝ) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • quadraticPrimeWeight x t) =
      (Ioc 0 x).indicator
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((x : ℂ) - t) ^ 2 / 2) := by
  funext t
  by_cases ht : t ∈ Ioc 0 x
  · simp only [quadraticPrimeWeight, indicator_of_mem ht, smul_eq_mul, mul_div_assoc]
  · simp only [quadraticPrimeWeight, indicator_of_notMem ht, smul_zero]

theorem quadraticPrimeWeight_mellinConvergent (x : ℝ) (hx : 0 ≤ x)
    (s : ℂ) (hs : 0 < s.re) : MellinConvergent (quadraticPrimeWeight x) s := by
  have hi := (quadratic_power_intervalIntegrable x hx s hs).1
  have hg := hi.integrable_indicator measurableSet_Ioc
  unfold MellinConvergent
  rw [quadratic_mellin_integrand]
  exact hg.integrableOn

theorem mellin_quadraticPrimeWeight (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    mellin (quadraticPrimeWeight x) s = (x : ℂ) ^ (s + 2) / (s * (s + 1) * (s + 2)) := by
  unfold mellin
  rw [quadratic_mellin_integrand, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc 0 x ⊆ Ioi 0 from fun t ht => ht.1)]
  rw [← intervalIntegral.integral_of_le hx.le]
  exact integral_quadratic_power x hx s hs

lemma quadraticPrimeWeight_primeSum (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.vonMangoldt n : ℂ) * quadraticPrimeWeight x n) =
        (secondPsiPrimitive N x : ℂ) := by
  dsimp [secondPsiPrimitive]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  by_cases hnx : (n : ℝ) ≤ x
  · have hmem : (n : ℝ) ∈ Ioc 0 x := ⟨hn₀, hnx⟩
    rw [quadraticPrimeWeight, indicator_of_mem hmem, max_eq_left (sub_nonneg.mpr hnx)]
    push_cast
    ring
  · have hmem : (n : ℝ) ∉ Ioc 0 x := fun h => hnx h.2
    rw [quadraticPrimeWeight, indicator_of_notMem hmem,
      max_eq_right (by linarith : x - n ≤ 0)]
    simp

lemma cubic_zero_denominator_bound (s : ℂ) :
    |s.im| ^ 3 ≤ ‖s * (s + 1) * (s + 2)‖ := by
  have h₀ := Complex.abs_im_le_norm s
  have h₁ : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have h₂ : |s.im| ≤ ‖s + 2‖ := by simpa using Complex.abs_im_le_norm (s + 2)
  have hp := mul_le_mul (mul_le_mul h₀ h₁ (abs_nonneg _) (norm_nonneg _))
    h₂ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [norm_mul, pow_succ, pow_two, pow_zero, one_mul] using hp

theorem norm_quadratic_mellin_le (x : ℝ) (hx : 0 < x) (s : ℂ)
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    ‖mellin (quadraticPrimeWeight x) s‖ ≤ x ^ (s.re + 2) / |s.im| ^ 3 := by
  rw [mellin_quadraticPrimeWeight x hx s hs, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.re_ofNat]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (pow_pos (abs_pos.mpr him) 3)
    (cubic_zero_denominator_bound s)

end DusartSmoothing


