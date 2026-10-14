-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GaussianChange
-- name    : dusart_psi_433_20261014_GaussianChange
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:43:03.315545+00:00
-- url     : https://prove2.me/theorems/42700a57-18e8-4191-98fb-169068b28771
-- title:
--   Dusart smoothing: Gaussian Change
-- statement:
--   This module gives the complete gaussian change component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LowGaussian
noncomputable section
namespace DusartSmoothing
open Real Set MeasureTheory

lemma logarithmic_gaussian_integral_change (X a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (k : ℕ) (w : ℝ → ℝ) :
    (∫ t in a..b, w (Real.log t) * Real.exp (-X^2 / Real.log t) / t^(k + 1)) =
      ∫ u in Real.log a..Real.log b, w u * Real.exp (-(k : ℝ) * u + (-X^2 / u)) := by
  rw [← logarithmic_integral_change a b ha hab
    (fun u => w u * Real.exp (-(k : ℝ) * u + (-X^2 / u)))]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have htp : 0 < t := ha.trans_le ht.1
  have he : Real.exp (-(k : ℝ) * Real.log t) = (t^k)⁻¹ := by
    rw [show -(k : ℝ) * Real.log t = -((k : ℝ) * Real.log t) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log htp]
  change w (Real.log t) * Real.exp (-X^2 / Real.log t) / t^(k+1) = _
  simp only [Real.exp_add, he]
  rw [pow_succ]
  ring

lemma tail_gaussian_integral_change (X a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianTailZeroWeight X t) =
      (∫ u in Real.log a..Real.log b,
        (u - Real.log (2 * Real.pi)) * Real.exp (-2 * u + (-X^2 / u))) / (2 * Real.pi) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : (∫ t in a..b,
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianTailZeroWeight X t) =
      (∫ t in a..b,
        (Real.log t - Real.log (2 * Real.pi)) * Real.exp (-X^2 / Real.log t) / t^3) / (2 * Real.pi) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    change (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * gaussianTailZeroWeight X t = _
    rw [Real.log_div (ha.trans_le ht.1).ne' hpi.ne']
    dsimp [gaussianTailZeroWeight]
    ring
  rw [he]
  have hc := logarithmic_gaussian_integral_change X a b ha hab 2
    (fun u => u - Real.log (2 * Real.pi))
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hc
  rw [hc]

lemma gaussian_count_error_integral_change (X a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, gaussianTailZeroWeight X t / t) =
      ∫ u in Real.log a..Real.log b, Real.exp (-3 * u + (-X^2 / u)) := by
  have he : (∫ t in a..b, gaussianTailZeroWeight X t / t) =
      ∫ t in a..b, 1 * Real.exp (-X^2 / Real.log t) / t^(3 + 1) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [gaussianTailZeroWeight]
    ring
  rw [he]
  simpa only [Nat.cast_ofNat, one_mul] using
    logarithmic_gaussian_integral_change X a b ha hab 3 (fun _ => 1)

end DusartSmoothing


