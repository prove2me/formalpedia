-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GaussianWeights
-- name    : dusart_psi_433_20261014_GaussianWeights
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:50.989927+00:00
-- url     : https://prove2.me/theorems/0c7b947a-4460-478c-92c1-b706ff7bef31
-- title:
--   Dusart smoothing: Gaussian Weights
-- statement:
--   This module gives the complete gaussian weights component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Parameters
noncomputable section
namespace DusartSmoothing
open Real

noncomputable def gaussianZeroWeight (X t : ℝ) : ℝ := Real.exp (-X^2 / Real.log t) / t
noncomputable def gaussianTailZeroWeight (X t : ℝ) : ℝ := Real.exp (-X^2 / Real.log t) / t^3

lemma hasDerivAt_gaussian_exponent (X t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun y : ℝ => Real.exp (-X^2 / Real.log y))
      (Real.exp (-X^2 / Real.log t) * (X^2 / (t * (Real.log t)^2))) t := by
  have htp : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  convert (((hasDerivAt_const t (-X^2)).div (Real.hasDerivAt_log htp.ne') hl).exp) using 1 <;> try rfl
  dsimp
  field_simp <;> ring

lemma hasDerivAt_gaussianZeroWeight (X t : ℝ) (ht : 1 < t) :
    HasDerivAt (gaussianZeroWeight X)
      (Real.exp (-X^2 / Real.log t) * (X^2 / (Real.log t)^2 - 1) / t^2) t := by
  have htp : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  convert (hasDerivAt_gaussian_exponent X t ht).div (hasDerivAt_id t) htp.ne' using 1 <;> try rfl
  dsimp [gaussianZeroWeight]
  field_simp <;> ring

lemma hasDerivAt_gaussianTailZeroWeight (X t : ℝ) (ht : 1 < t) :
    HasDerivAt (gaussianTailZeroWeight X)
      (Real.exp (-X^2 / Real.log t) * (X^2 / (Real.log t)^2 - 3) / t^4) t := by
  have htp : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  convert (hasDerivAt_gaussian_exponent X t ht).div ((hasDerivAt_id t).pow 3)
    (pow_ne_zero 3 htp.ne') using 1 <;> try rfl
  dsimp [gaussianTailZeroWeight]
  field_simp <;> ring

lemma gaussianZeroWeight_deriv_nonneg (X t : ℝ) (ht : 1 < t) (hl : Real.log t ≤ X) :
    0 ≤ deriv (gaussianZeroWeight X) t := by
  have hp : 0 < Real.log t := Real.log_pos ht
  have hX : 0 < X := hp.trans_le hl
  have hs : (Real.log t)^2 ≤ X^2 := by nlinarith
  have hc : 0 ≤ X^2 / (Real.log t)^2 - 1 := by
    have hh : (1 : ℝ) ≤ X^2 / (Real.log t)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hp)).2 (by simpa using hs)
    linarith
  rw [(hasDerivAt_gaussianZeroWeight X t ht).deriv]
  exact div_nonneg (mul_nonneg (Real.exp_nonneg _) hc) (sq_nonneg _)

lemma gaussianTailZeroWeight_deriv_neg (X ν t : ℝ) (hX : 0 < X)
    (hν : (97 / 100 : ℝ) < ν) (ht : 1 < t) (hl : X * ν ≤ Real.log t) :
    deriv (gaussianTailZeroWeight X) t < 0 := by
  have hp : 0 < Real.log t := Real.log_pos ht
  have hνp : 0 < ν := by linarith
  have hs : (X * ν)^2 ≤ (Real.log t)^2 :=
    (sq_le_sq₀ (mul_nonneg hX.le hνp.le) hp.le).2 hl
  have hm : 0 < X^2 * (3 * ν^2 - 1) := mul_pos (sq_pos_of_pos hX) (by nlinarith)
  have hc : X^2 / (Real.log t)^2 - 3 < 0 := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hp)).2 (show X^2 < 3 * (Real.log t)^2 by nlinarith)
    linarith
  rw [(hasDerivAt_gaussianTailZeroWeight X t ht).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) hc) (by positivity)

end DusartSmoothing


