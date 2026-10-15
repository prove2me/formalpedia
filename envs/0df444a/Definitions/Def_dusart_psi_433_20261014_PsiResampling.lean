-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PsiResampling
-- name    : dusart_psi_433_20261014_PsiResampling
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T12:16:59.887712+00:00
-- url     : https://prove2.me/theorems/9e456845-b59e-46d6-b32d-e414c199e014
-- title:
--   Dusart smoothing: Psi Resampling
-- statement:
--   This module gives the complete psi resampling component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ResamplingNorm
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PerronLoss
noncomputable section
namespace DusartSmoothing
open Real

lemma double_average_resampling_error (R x ν a : ℝ) (hR : 0 < R) (hx : 0 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed (X R x) ≤ ν)
    (hk : k (X R x) ν = 1) (ha : 1 ≤ a)
    (hab : a + 2 * (optimalWidth (X R x) ν * x) ≤ x * (1 + 2 * optimalWidth (X R x) ν)) :
    |doubleBoxAverage Chebyshev.psi a (optimalWidth (X R x) ν * x) - (a + optimalWidth (X R x) ν * x)| <
      optimalWidth (X R x) ν * x * ((1 + 2 * optimalWidth (X R x) ν)^3 +
        Real.sqrt (X R x) * Real.exp (-X R x)) := by
  have hf := threshold_facts R x hR hX
  have hx1 : 1 < x := by rw [← Real.exp_log hx]; exact Real.one_lt_exp_iff.mpr hf.2.1
  have hx8 : Real.exp (8 * X R x) ≤ x := by
    have h := Real.exp_le_exp.mpr hf.2.2.2.le
    rwa [Real.exp_log hx] at h
  have hδ := optimalWidth_pos (X R x) ν hf.1 hν
  have hh := mul_pos hδ hx
  have hδsmall := optimalWidth_lt_one_thousandth (X R x) ν hf.1 hν hν1 hk
  have hψ := doubleBoxAverage_psi_error_zero_sum a (optimalWidth (X R x) ν * x) ha hh
  have hz := resampling_zero_series_norm_bound R x ν a hR hx1 hzero hX hν hν1 hseed hk ha hab
  have hr := smoothing_perron_remainder_le x (optimalWidth (X R x) ν) a hx1.le hδ
    (by linarith) ha hab
  have hl := elementary_perron_loss_absorbed (X R x) ν x hf.1 hν hν1 hk hx8
  have he : optimalWidth (X R x) ν * x * ((1 + 2 * optimalWidth (X R x) ν)^3 +
      Real.sqrt (X R x) * Real.exp (-X R x)) =
      x * (1 + 2 * optimalWidth (X R x) ν)^3 * optimalWidth (X R x) ν +
        optimalWidth (X R x) ν * x * (Real.sqrt (X R x) * Real.exp (-X R x)) := by ring
  rw [he]
  linarith

end DusartSmoothing


