-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ArithmeticKernels
-- name    : dusart_psi_433_20261014_ArithmeticKernels
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:55.061416+00:00
-- url     : https://prove2.me/theorems/9931b0fb-b7c4-4f17-9cd6-5c75e9ab50d0
-- title:
--   Dusart smoothing: Arithmetic Kernels
-- statement:
--   This module gives the complete arithmetic kernels component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PsiComparison
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace DusartSmoothing

noncomputable def primeStep (c t : ℝ) : ℝ := if c ≤ t then 1 else 0

lemma primeStep_mono (c : ℝ) : Monotone (primeStep c) := by
  intro x y hxy
  dsimp [primeStep]
  split_ifs with hx hy
  · norm_num
  · exact False.elim (hy (hx.trans hxy))
  · norm_num
  · norm_num

lemma integral_primeStep (c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, primeStep c t) = max (h - c) 0 - max (-c) 0 := by
  by_cases hc : c ≤ 0
  · have he : (∫ t in (0 : ℝ)..h, primeStep c t) = ∫ _ in (0 : ℝ)..h, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hh] at ht
      simp only [primeStep, if_pos (hc.trans ht.1)]
    rw [he, intervalIntegral.integral_const]
    rw [max_eq_left (by linarith : 0 ≤ h - c), max_eq_left (by linarith : 0 ≤ -c)]
    simp only [sub_zero, smul_eq_mul, mul_one]
    ring
  have hcp : 0 < c := lt_of_not_ge hc
  by_cases hch : h ≤ c
  · have he : (∫ t in (0 : ℝ)..h, primeStep c t) = ∫ _ in (0 : ℝ)..h, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh
      intro t ht
      simp only [primeStep, if_neg (not_le.mpr (ht.2.trans_le hch))]
    rw [he, intervalIntegral.integral_zero, max_eq_right (by linarith : h - c ≤ 0),
      max_eq_right (by linarith : -c ≤ 0), sub_self]
  have hchp : c < h := lt_of_not_ge hch
  have hl : (∫ t in (0 : ℝ)..c, primeStep c t) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hcp.le
        intro t ht
        simp only [primeStep, if_neg (not_le.mpr ht.2)]
      _ = 0 := intervalIntegral.integral_zero
  have hu : (∫ t in c..h, primeStep c t) = h - c := by
    calc
      _ = ∫ _ in c..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hchp.le] at ht
        simp only [primeStep, if_pos ht.1]
      _ = h - c := by simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((primeStep_mono c).intervalIntegrable (a := 0) (b := c))
    ((primeStep_mono c).intervalIntegrable (a := c) (b := h))
  rw [← hadd, hl, hu, max_eq_left (sub_nonneg.mpr hchp.le),
    max_eq_right (by linarith : -c ≤ 0)]
  ring

lemma integral_linear (a b c : ℝ) :
    (∫ t in a..b, t - c) = (b ^ 2 - a ^ 2) / 2 - (b - a) * c := by
  have he : (∫ t in a..b, t - c) = (∫ t in a..b, t) - (∫ _ in a..b, c) := by
    exact intervalIntegral.integral_sub (continuous_id.intervalIntegrable a b)
      intervalIntegrable_const
  rw [he]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]

lemma integral_ramp (c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, max (t - c) 0) =
      (max (h - c) 0 ^ 2 - max (-c) 0 ^ 2) / 2 := by
  have hi (a b : ℝ) : IntervalIntegrable (fun t : ℝ => max (t - c) 0) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => max (t - c) 0)).intervalIntegrable a b
  by_cases hc : c ≤ 0
  · have he : (∫ t in (0 : ℝ)..h, max (t - c) 0) = ∫ t in (0 : ℝ)..h, t - c := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hh] at ht
      exact max_eq_left (by linarith [ht.1])
    rw [he, integral_linear, max_eq_left (by linarith : 0 ≤ h - c),
      max_eq_left (by linarith : 0 ≤ -c)]
    ring
  have hcp : 0 < c := lt_of_not_ge hc
  by_cases hch : h ≤ c
  · have he : (∫ t in (0 : ℝ)..h, max (t - c) 0) = ∫ _ in (0 : ℝ)..h, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hh] at ht
      exact max_eq_right (by linarith [ht.2])
    rw [he, intervalIntegral.integral_zero, max_eq_right (by linarith : h - c ≤ 0),
      max_eq_right (by linarith : -c ≤ 0)]
    norm_num
  have hchp : c < h := lt_of_not_ge hch
  have hl : (∫ t in (0 : ℝ)..c, max (t - c) 0) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hcp.le] at ht
        exact max_eq_right (by linarith [ht.2])
      _ = 0 := intervalIntegral.integral_zero
  have hu : (∫ t in c..h, max (t - c) 0) = (h - c) ^ 2 / 2 := by
    calc
      _ = ∫ t in c..h, t - c := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hchp.le] at ht
        exact max_eq_left (by linarith [ht.1])
      _ = (h - c) ^ 2 / 2 := by rw [integral_linear]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c h), hl, hu,
    max_eq_left (sub_nonneg.mpr hchp.le), max_eq_right (by linarith : -c ≤ 0)]
  ring

lemma integral_primeStep_shift (x c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, primeStep c (x + t)) =
      max (x + h - c) 0 - max (x - c) 0 := by
  have he : (fun t => primeStep c (x + t)) = primeStep (c - x) := by
    funext t
    dsimp [primeStep]
    have hcond : (c ≤ x + t) ↔ c - x ≤ t := by constructor <;> intro ht <;> linarith
    simp only [hcond]
  rw [he, integral_primeStep (c - x) h hh]
  rw [show h - (c - x) = x + h - c by ring, show -(c - x) = x - c by ring]

lemma integral_ramp_shift (x c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, max (x + t - c) 0) =
      (max (x + h - c) 0 ^ 2 - max (x - c) 0 ^ 2) / 2 := by
  have he : (fun t : ℝ => max (x + t - c) 0) = (fun t => max (t - (c - x)) 0) := by
    funext t
    congr 1
    ring
  rw [he, integral_ramp (c - x) h hh]
  rw [show h - (c - x) = x + h - c by ring, show -(c - x) = x - c by ring]

theorem double_integral_primeStep (x c h : ℝ) (hh : 0 ≤ h) :
    (∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, primeStep c (x + u + v)) =
      (max (x + 2 * h - c) 0 ^ 2 - 2 * max (x + h - c) 0 ^ 2 +
        max (x - c) 0 ^ 2) / 2 := by
  have he : (fun u : ℝ => ∫ v in (0 : ℝ)..h, primeStep c (x + u + v)) =
      (fun u => max (x + u + h - c) 0 - max (x + u - c) 0) := by
    funext u
    exact integral_primeStep_shift (x + u) c h hh
  rw [he]
  have hs : (∫ u in (0 : ℝ)..h, max (x + u + h - c) 0 - max (x + u - c) 0) =
      (∫ u in (0 : ℝ)..h, max (x + u + h - c) 0) -
        (∫ u in (0 : ℝ)..h, max (x + u - c) 0) := by
    exact intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun u : ℝ => max (x + u + h - c) 0)).intervalIntegrable 0 h)
      ((by fun_prop : Continuous (fun u : ℝ => max (x + u - c) 0)).intervalIntegrable 0 h)
  rw [hs]
  have hr : (∫ u in (0 : ℝ)..h, max (x + u + h - c) 0) =
      (max (x + 2 * h - c) 0 ^ 2 - max (x + h - c) 0 ^ 2) / 2 := by
    have hab : (fun u : ℝ => max (x + u + h - c) 0) =
        (fun u => max (x + h + u - c) 0) := by
      funext u
      rw [show x + u + h - c = x + h + u - c by ring]
    rw [hab, integral_ramp_shift (x + h) c h hh,
      show x + h + h - c = x + 2 * h - c by ring]
  rw [hr, integral_ramp_shift x c h hh]
  ring

end DusartSmoothing


