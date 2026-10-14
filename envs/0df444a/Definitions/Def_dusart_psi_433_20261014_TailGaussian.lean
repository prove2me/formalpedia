-- Prove2me | Definitions.Def_dusart_psi_433_20261014_TailGaussian
-- name    : dusart_psi_433_20261014_TailGaussian
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:44:36.297042+00:00
-- url     : https://prove2.me/theorems/55ed5ea1-6836-4049-98fa-32beffe49ce1
-- title:
--   Dusart smoothing: Tail Gaussian
-- statement:
--   This module gives the complete tail gaussian component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_DecreasingWeight
import Definitions.Def_dusart_psi_433_20261014_GaussianChange
import Definitions.Def_dusart_psi_433_20261014_CountTailEnvelope
noncomputable section
namespace DusartSmoothing
open Real Set MeasureTheory

lemma actual_tail_gaussian_zero_bound (X ν B : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hB : transformHeight X ν ≤ B) :
    (∑ ρ ∈ (RvM.finite_zero_window (a := transformHeight X ν) (b := B)
      (transformHeight_pos X ν)).toFinset,
      (RvM.zeroMult ρ : ℝ) * gaussianTailZeroWeight X ρ.im) ≤
      upperEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) +
        2 * zeroCountErrorBound (transformHeight X ν) * gaussianTailZeroWeight X (transformHeight X ν) +
        9 * gaussianCountTailEnvelope X (X * ν) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hu : Real.log (2 * Real.pi) ≤ X * ν := by
    nlinarith [log_two_pi_bounds.2, mul_pos (by linarith : 0 < X - 836 / 100)
      (by linarith : 0 < ν - 97 / 100)]
  have hu' : 2 * Real.log (2 * Real.pi) - 1 ≤ X * ν := by
    nlinarith [log_two_pi_bounds.2, mul_pos (by linarith : 0 < X - 836 / 100)
      (by linarith : 0 < ν - 97 / 100)]
  have hT : 2 * Real.pi ≤ transformHeight X ν := by
    rw [transformHeight, ← Real.exp_log (by positivity : 0 < 2 * Real.pi)]
    exact Real.exp_le_exp.mpr hu
  have hT4 : 4 ≤ transformHeight X ν := by linarith [Real.pi_gt_three]
  have hlogB : X * ν ≤ Real.log B := by
    have h := Real.log_le_log (transformHeight_pos X ν) hB
    rwa [transformHeight, Real.log_exp] at h
  have hD2 : 0 < 2 * (X * ν)^2 - X^2 := by
    have h := mul_pos (sq_pos_of_pos hXp) (show 0 < 2 * ν^2 - 1 by nlinarith)
    nlinarith
  have hD3 : 0 < 3 - X^2 / (X * ν)^2 := by
    have he : X^2 / (X * ν)^2 = 1 / ν^2 := by field_simp [hXp.ne', hνp.ne'] <;> ring
    rw [he]
    have h := (div_lt_iff₀ (sq_pos_of_pos hνp)).2 (show (1 : ℝ) < 3 * ν^2 by nlinarith)
    linarith
  let g' : ℝ → ℝ := fun t => Real.exp (-X^2 / Real.log t) *
    (X^2 / (Real.log t)^2 - 3) / t^4
  have ht1 : ∀ t ∈ Icc (transformHeight X ν) B, 1 < t := by
    intro t ht; linarith [hT4, ht.1]
  have hd : ∀ t ∈ Icc (transformHeight X ν) B,
      HasDerivAt (gaussianTailZeroWeight X) (g' t) t :=
    fun t ht => hasDerivAt_gaussianTailZeroWeight X t (ht1 t ht)
  have hgc : ContinuousOn (gaussianTailZeroWeight X) (Icc (transformHeight X ν) B) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn g' (Icc (transformHeight X ν) B) := by
    intro t ht
    have htn : t ≠ 0 := by linarith [ht1 t ht]
    have hln : Real.log t ≠ 0 := (Real.log_pos (ht1 t ht)).ne'
    have htn4 := pow_ne_zero 4 htn
    have hln2 := pow_ne_zero 2 hln
    dsimp [g']
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hg : ∀ t ∈ Icc (transformHeight X ν) B, 0 ≤ gaussianTailZeroWeight X t := by
    intro t ht
    exact div_nonneg (Real.exp_nonneg _) (pow_nonneg (by linarith [ht1 t ht]) 3)
  have hgp : ∀ t ∈ Icc (transformHeight X ν) B, g' t ≤ 0 := by
    intro t ht
    rw [← (hd t ht).deriv]
    have hl : X * ν ≤ Real.log t := by
      have h := Real.log_le_log (transformHeight_pos X ν) ht.1
      rwa [transformHeight, Real.log_exp] at h
    exact (gaussianTailZeroWeight_deriv_neg X ν t hXp hν (ht1 t ht) hl).le
  have hiM : IntervalIntegrable (fun t => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) *
      gaussianTailZeroWeight X t) volume (transformHeight X ν) B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hB
    apply ContinuousOn.mul _ hgc
    intro t ht
    have htn : t ≠ 0 := by linarith [ht1 t ht]
    have hden : t / (2 * Real.pi) ≠ 0 := div_ne_zero htn (by positivity)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hiE : IntervalIntegrable (fun t => 9 / (t + 5) * gaussianTailZeroWeight X t)
      volume (transformHeight X ν) B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hB
    apply ContinuousOn.mul _ hgc
    intro t ht
    have hn : t + 5 ≠ 0 := by linarith [ht1 t ht]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hiP : IntervalIntegrable (fun t => gaussianTailZeroWeight X t / t)
      volume (transformHeight X ν) B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hB
    exact hgc.div continuousOn_id (fun t ht => by change t ≠ 0; linarith [ht1 t ht])
  have hs := actual_decreasing_zero_weight_bound (transformHeight X ν) B hT4 hB
    (gaussianTailZeroWeight X) g' hc hd hg hgp
  have he : (∫ t in (transformHeight X ν)..B,
      ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) + 9 / (t + 5)) * gaussianTailZeroWeight X t) =
      (∫ t in (transformHeight X ν)..B, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianTailZeroWeight X t) +
      (∫ t in (transformHeight X ν)..B, 9 / (t + 5) * gaussianTailZeroWeight X t) := by
    rw [← intervalIntegral.integral_add hiM hiE]
    apply intervalIntegral.integral_congr
    intro t _; dsimp; ring
  rw [he] at hs
  have hmain : (∫ t in (transformHeight X ν)..B,
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianTailZeroWeight X t) ≤
      upperEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) := by
    rw [tail_gaussian_integral_change X _ B (transformHeight_pos X ν) hB, transformHeight, Real.log_exp]
    exact div_le_div_of_nonneg_right
      (upper_kernel_integral_bound X (Real.log (2 * Real.pi)) (X * ν) (Real.log B)
        (mul_pos hXp hνp) hu hu' hD2 hlogB) (by positivity)
  have herror : (∫ t in (transformHeight X ν)..B, 9 / (t + 5) * gaussianTailZeroWeight X t) ≤
      9 * gaussianCountTailEnvelope X (X * ν) := by
    have hm : (∫ t in (transformHeight X ν)..B, 9 / (t + 5) * gaussianTailZeroWeight X t) ≤
        9 * ∫ t in (transformHeight X ν)..B, gaussianTailZeroWeight X t / t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hB hiE (hiP.const_mul 9)
      intro t ht
      have htp : 0 < t := by linarith [ht1 t ht]
      calc
        9 / (t + 5) * gaussianTailZeroWeight X t ≤ 9 / t * gaussianTailZeroWeight X t := by
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 9) htp (by linarith)) (hg t ht)
        _ = 9 * (gaussianTailZeroWeight X t / t) := by ring
    rw [gaussian_count_error_integral_change X _ B (transformHeight_pos X ν) hB,
      transformHeight, Real.log_exp] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left
      (gaussian_count_error_kernel_bound X (X * ν) (Real.log B) (mul_pos hXp hνp) hlogB hD3)
      (by norm_num))
  linarith

end DusartSmoothing


