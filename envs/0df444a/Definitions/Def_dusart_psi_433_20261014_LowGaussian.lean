-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LowGaussian
-- name    : dusart_psi_433_20261014_LowGaussian
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:41:05.107882+00:00
-- url     : https://prove2.me/theorems/b9106fde-f470-41d5-9672-7153a9a9c8f9
-- title:
--   Dusart smoothing: Low Gaussian
-- statement:
--   This module gives the complete low gaussian component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_IncreasingWeight
import Definitions.Def_dusart_psi_433_20261014_GaussianWeights
import Definitions.Def_dusart_psi_433_20261014_SharperKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
namespace DusartSmoothing
open Real Set MeasureTheory

lemma logarithmic_integral_change (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) :
    (∫ t in a..b, g (Real.log t) / t) = ∫ u in Real.log a..Real.log b, g u := by
  have hc : ContinuousOn Real.log (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_id.log (fun t ht => (ha.trans_le ht.1).ne')
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := Real.log) (f' := fun t => 1 / t) (g := g) hc
    (fun t ht => by
      simpa only [one_div] using Real.hasDerivAt_log (by
        rw [min_eq_left hab, max_eq_right hab] at ht
        exact (ha.trans ht.1).ne'))
    (fun t ht => by
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact one_div_nonneg.mpr (ha.trans ht.1).le)
  simpa only [Function.comp_apply, mul_one_div] using h

lemma lower_gaussian_integral_change (X T : ℝ) (hT : 2 * Real.pi ≤ T) :
    (∫ t in (2 * Real.pi)..T,
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianZeroWeight X t) =
      (∫ u in Real.log (2 * Real.pi)..Real.log T,
        (u - Real.log (2 * Real.pi)) * Real.exp (-X^2 / u)) / (2 * Real.pi) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : (∫ t in (2 * Real.pi)..T,
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianZeroWeight X t) =
      (∫ t in (2 * Real.pi)..T,
        ((Real.log t - Real.log (2 * Real.pi)) * Real.exp (-X^2 / Real.log t)) / t) /
        (2 * Real.pi) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : t ≠ 0 := (hpi.trans_le ht.1).ne'
    change (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianZeroWeight X t = _
    rw [Real.log_div ht0 hpi.ne']
    dsimp [gaussianZeroWeight]
    ring
  rw [he, logarithmic_integral_change (2 * Real.pi) T hpi hT
    (fun u => (u - Real.log (2 * Real.pi)) * Real.exp (-X^2 / u))]

lemma actual_low_gaussian_zero_bound (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) :
    (∑ ρ ∈ (RvM.finite_zero_window (b := transformHeight X ν)
      (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * gaussianZeroWeight X ρ.im) ≤
      improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) +
        2 * (9 * Real.log (transformHeight X ν + 5) + 79) *
          gaussianZeroWeight X (transformHeight X ν) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  have ha : 0 < Real.log (2 * Real.pi) := by linarith [log_two_pi_bounds.1]
  have hu : Real.log (2 * Real.pi) ≤ X * ν := by
    nlinarith [log_two_pi_bounds.2, mul_pos (by linarith : 0 < X - 836 / 100)
      (by linarith : 0 < ν - 97 / 100)]
  have hT : 2 * Real.pi ≤ transformHeight X ν := by
    rw [transformHeight, ← Real.exp_log hpi]
    exact Real.exp_le_exp.mpr hu
  let g' : ℝ → ℝ := fun t => Real.exp (-X^2 / Real.log t) *
    (X^2 / (Real.log t)^2 - 1) / t^2
  have ht1 : ∀ t ∈ Icc (2 * Real.pi) (transformHeight X ν), 1 < t := by
    intro t ht; linarith [ht.1, Real.pi_gt_three]
  have hc : ContinuousOn g' (Icc (2 * Real.pi) (transformHeight X ν)) := by
    intro t ht
    have htn : t ≠ 0 := by linarith [ht1 t ht]
    have hln : Real.log t ≠ 0 := (Real.log_pos (ht1 t ht)).ne'
    have htn2 := pow_ne_zero 2 htn
    have hln2 := pow_ne_zero 2 hln
    dsimp [g']
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hd : ∀ t ∈ Icc (2 * Real.pi) (transformHeight X ν), HasDerivAt (gaussianZeroWeight X) (g' t) t :=
    fun t ht => hasDerivAt_gaussianZeroWeight X t (ht1 t ht)
  have hg : ∀ t ∈ Icc (2 * Real.pi) (transformHeight X ν), 0 ≤ gaussianZeroWeight X t := by
    intro t ht
    exact div_nonneg (Real.exp_nonneg _) (by linarith [ht1 t ht])
  have hgp : ∀ t ∈ Icc (2 * Real.pi) (transformHeight X ν), 0 ≤ g' t := by
    intro t ht
    have hl : Real.log t ≤ X := by
      have h := Real.log_le_log (by linarith [ht1 t ht]) ht.2
      rw [transformHeight, Real.log_exp] at h
      nlinarith [mul_nonneg hXp.le (sub_nonneg.mpr hν1)]
    rw [← (hd t ht).deriv]
    exact gaussianZeroWeight_deriv_nonneg X t (ht1 t ht) hl
  have hs := actual_increasing_zero_weight_bound (transformHeight X ν) hT
    (gaussianZeroWeight X) g' hc hd hg hgp
  rw [lower_gaussian_integral_change X _ hT, transformHeight, Real.log_exp] at hs
  have hi := improved_lower_kernel_integral_bound X (Real.log (2 * Real.pi)) (X * ν) ha hu
  exact hs.trans (add_le_add (div_le_div_of_nonneg_right hi hpi.le) le_rfl)

end DusartSmoothing


