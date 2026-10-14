-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaZeroConstant
-- name    : dusart_psi_433_20261014_ZetaZeroConstant
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:46.721469+00:00
-- url     : https://prove2.me/theorems/48bde673-4773-4532-8649-2b02f82cbf48
-- title:
--   Dusart smoothing: Zeta Zero Constant
-- statement:
--   This module gives the complete zeta zero constant component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Parameters
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section
namespace DusartSmoothing
open Complex Real

lemma logDeriv_zeta_zero : logDeriv riemannZeta 0 = (Real.log (2 * Real.pi) : ℂ) := by
  rw [logDeriv_apply, deriv_riemannZeta_zero, riemannZeta_zero]
  have he : (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

lemma norm_logDeriv_zeta_zero_lt_two : ‖logDeriv riemannZeta 0‖ < 2 := by
  rw [logDeriv_zeta_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [log_two_pi_bounds.1] : 0 ≤ Real.log (2 * Real.pi))]
  exact log_two_pi_bounds.2

end DusartSmoothing


