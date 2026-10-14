-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
-- name    : dusart_psi_433_20261014_PsiZeroSum
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T10:10:27.180309+00:00
-- url     : https://prove2.me/theorems/ad29d2b3-6188-42c3-ba12-665388a90452
-- title:
--   Dusart smoothing: Psi Zero Sum
-- statement:
--   This module gives the complete psi zero sum component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_CoefficientBounds
noncomputable section
namespace DusartSmoothing
open Complex Real MeasureTheory

lemma doubleBoxAverage_psi_error_zero_sum (x h : ℝ) (hx : 1 ≤ x) (hh : 0 < h) :
    |doubleBoxAverage Chebyshev.psi x h - (x + h)| ≤
      2 + (∑' ρ : NontrivialZetaZero,
        ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val‖) +
      512 * (x + 2 * h) ^ (3 / 2 : ℝ) / h^2 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 2 * h)
  have he := doubleBoxAverage_psi_explicit_formula N x h hx hh hN
  have he' : ((doubleBoxAverage Chebyshev.psi x h - (x + h) : ℝ) : ℂ) =
      -logDeriv riemannZeta 0 -
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val) +
      (perronLeftRemainder (x + 2 * h) - 2 * perronLeftRemainder (x + h) +
        perronLeftRemainder x) / (h : ℂ)^2 := by
    rw [Complex.ofReal_sub, he]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he']
  have hp := norm_logDeriv_zeta_zero_lt_two
  have hs := norm_tsum_le_tsum_norm (smoothed_zero_series_summable x h hx hh).norm
  have hr := norm_smoothed_perron_remainder x h (by linarith) hh
  have hn := (norm_add_le
    (-logDeriv riemannZeta 0 -
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val))
    ((perronLeftRemainder (x + 2 * h) - 2 * perronLeftRemainder (x + h) +
      perronLeftRemainder x) / (h : ℂ)^2)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_neg] at hn
  linarith

end DusartSmoothing


