-- Prove2me | Definitions.Def_dusart_psi_433_20261014_FinalExponent
-- name    : dusart_psi_433_20261014_FinalExponent
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:59.739998+00:00
-- url     : https://prove2.me/theorems/9b64ef43-5f81-4df8-be3a-3dd29359119e
-- title:
--   Dusart smoothing: Final Exponent
-- statement:
--   This module gives the complete final exponent component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WidthElementary
noncomputable section
namespace DusartSmoothing
open Real

lemma final_smoothing_exponential_bound (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hδb : δ ≤ (4 / 5 : ℝ) * b) :
    (1 + 2 * δ)^3 + b + 1 < 2 * Real.exp ((591 / 100 : ℝ) * b) := by
  have hA : 0 ≤ 1 + 2 * δ := by positivity
  have hE : 1 + 2 * δ ≤ Real.exp (2 * δ) := by
    linarith [Real.add_one_le_exp (2 * δ)]
  have hcube := pow_le_pow_left₀ hA hE 3
  have hE3 : Real.exp (2 * δ)^3 = Real.exp (6 * δ) := by
    rw [← Real.exp_nat_mul]; congr 1 <;> norm_num <;> ring
  rw [hE3] at hcube
  have hm : (1 + 2 * δ)^3 ≤ Real.exp ((24 / 5 : ℝ) * b) :=
    hcube.trans (Real.exp_le_exp.mpr (by linarith))
  have h1 : 1 ≤ Real.exp ((24 / 5 : ℝ) * b) := Real.one_le_exp_iff.mpr (by positivity)
  have hd : 1 + (111 / 100 : ℝ) * b ≤ Real.exp ((111 / 100 : ℝ) * b) := by
    linarith [Real.add_one_le_exp ((111 / 100 : ℝ) * b)]
  have hh := mul_le_mul_of_nonneg_left hd (Real.exp_nonneg ((24 / 5 : ℝ) * b))
  have he : Real.exp ((24 / 5 : ℝ) * b) * Real.exp ((111 / 100 : ℝ) * b) =
      Real.exp ((591 / 100 : ℝ) * b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hh
  have hprod := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ (111 / 100 : ℝ) * b)
  nlinarith only [hm, h1, hh, hprod, hb]

end DusartSmoothing


