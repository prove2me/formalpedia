-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ResamplingCoefficients
-- name    : dusart_psi_433_20261014_ResamplingCoefficients
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T10:07:59.689409+00:00
-- url     : https://prove2.me/theorems/8697626c-3b46-4bcf-ac3a-b0a95c3336ef
-- title:
--   Dusart smoothing: Resampling Coefficients
-- statement:
--   This module gives the complete resampling coefficients component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PerronKernelConj
import Definitions.Def_dusart_psi_433_20261014_CoefficientBounds
import Definitions.Def_dusart_psi_433_20261014_ResamplingWeights
noncomputable section
namespace DusartSmoothing
open Real Complex Set

lemma smoothing_interval_power_bound (x δ a : ℝ) (hx : 0 < x) (hδ : 0 < δ)
    (ha : 0 < a) (hab : a + 2 * (δ * x) ≤ x * (1 + 2 * δ))
    (ρ : ℂ) (hρ : RvM.IsNontrivialZero ρ) (y : ℝ) (hy : y ∈ Icc a (a + 2 * (δ * x))) :
    ‖(y : ℂ)^ρ‖ ≤ ‖(x : ℂ)^ρ‖ * (1 + 2 * δ) := by
  have hyp : 0 < y := ha.trans_le hy.1
  have hA : 1 ≤ 1 + 2 * δ := by linarith
  rw [norm_cpow_eq_rpow_re_of_pos hyp, norm_cpow_eq_rpow_re_of_pos hx]
  calc
    y ^ ρ.re ≤ (x * (1 + 2 * δ)) ^ ρ.re :=
      Real.rpow_le_rpow hyp.le (hy.2.trans hab) hρ.2.1.le
    _ = x ^ ρ.re * (1 + 2 * δ) ^ ρ.re := Real.mul_rpow hx.le (by linarith)
    _ ≤ x ^ ρ.re * (1 + 2 * δ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_self_of_one_le hA hρ.2.2.le) (Real.rpow_nonneg hx.le _)

lemma norm_smoothed_kernel_resampling_bound (x δ a T : ℝ) (hx : 0 < x) (hδ : 0 < δ)
    (ha : 0 < a) (hab : a + 2 * (δ * x) ≤ x * (1 + 2 * δ))
    (ρ : ℂ) (hρ : RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im) :
    ‖smoothedZeroKernel a (δ * x) ρ‖ ≤
      (1 + 2 * δ)^3 * ‖(x : ℂ)^ρ‖ * resamplingZeroWeight δ T ρ.im := by
  have hh : 0 < δ * x := mul_pos hδ hx
  have hA : 1 ≤ 1 + 2 * δ := by linarith
  have hAp : 0 < 1 + 2 * δ := by linarith
  have hM : 0 ≤ ‖(x : ℂ)^ρ‖ * (1 + 2 * δ) := by positivity
  have hp := smoothing_interval_power_bound x δ a hx hδ ha hab ρ hρ
  unfold resamplingZeroWeight
  split_ifs with hlow
  · have hl := norm_smoothedZeroKernel_low a (δ * x) (‖(x : ℂ)^ρ‖ * (1 + 2 * δ)) hh hM ρ hρ.2.1
      (by simpa only [abs_of_pos hi] using hi) hp
    rw [abs_of_pos hi] at hl
    have hA3 : 1 + 2 * δ ≤ (1 + 2 * δ)^3 := by nlinarith [sq_nonneg δ]
    apply hl.trans
    have hm := mul_le_mul_of_nonneg_left hA3 (norm_nonneg ((x : ℂ)^ρ))
    have hd := div_le_div_of_nonneg_right hm hi.le
    convert hd using 1 <;> first | rfl | ring
  · have hu := norm_smoothedZeroKernel_high a (δ * x) (‖(x : ℂ)^ρ‖ * (1 + 2 * δ)) ha hh hM ρ
      (by simpa only [abs_of_pos hi] using hi) hp
    rw [abs_of_pos hi] at hu
    have hupper : 4 * (‖(x : ℂ)^ρ‖ * (1 + 2 * δ)) * (a + 2 * (δ * x))^2 /
        ((δ * x)^2 * ρ.im^3) ≤
        4 * (‖(x : ℂ)^ρ‖ * (1 + 2 * δ)) * (x * (1 + 2 * δ))^2 /
        ((δ * x)^2 * ρ.im^3) := by
      gcongr
    have he : 4 * (‖(x : ℂ)^ρ‖ * (1 + 2 * δ)) * (x * (1 + 2 * δ))^2 /
        ((δ * x)^2 * ρ.im^3) =
        (1 + 2 * δ)^3 * ‖(x : ℂ)^ρ‖ * (4 / (δ^2 * ρ.im^3)) := by
      field_simp [hx.ne'] <;> ring
    exact hu.trans (hupper.trans_eq he)

lemma smoothedZeroKernel_conj (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (ρ : ℂ) :
    smoothedZeroKernel a h (starRingEnd ℂ ρ) = starRingEnd ℂ (smoothedZeroKernel a h ρ) := by
  rw [smoothedZeroKernel, smoothedZeroKernel, quadraticKernel_conj _ (by linarith),
    quadraticKernel_conj _ (by linarith), quadraticKernel_conj a ha]
  simp only [map_div₀, map_add, map_sub, map_mul, map_ofNat, map_pow, conj_ofReal]

lemma norm_weighted_smoothed_conj (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (ρ : ℂ) (hρ : ρ ≠ 1) :
    ‖(RvM.zeroMult (starRingEnd ℂ ρ) : ℂ) * smoothedZeroKernel a h (starRingEnd ℂ ρ)‖ =
      ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a h ρ‖ := by
  rw [RvM.zeroMult_conj ρ hρ, smoothedZeroKernel_conj a h ha hh ρ]
  have he : (RvM.zeroMult ρ : ℂ) * starRingEnd ℂ (smoothedZeroKernel a h ρ) =
      starRingEnd ℂ ((RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a h ρ) := by simp
  rw [he, Complex.norm_conj]

end DusartSmoothing


