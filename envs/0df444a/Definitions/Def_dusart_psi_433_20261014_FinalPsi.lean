-- Prove2me | Definitions.Def_dusart_psi_433_20261014_FinalPsi
-- name    : dusart_psi_433_20261014_FinalPsi
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T12:19:43.723147+00:00
-- url     : https://prove2.me/theorems/e4f84933-8f1b-4c5a-8c4b-5c0244608f47
-- title:
--   Dusart smoothing: Final Psi
-- statement:
--   This module gives the complete final psi component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PsiResampling
import Definitions.Def_dusart_psi_433_20261014_FinalExponent
noncomputable section
namespace DusartSmoothing
open Real

theorem dusart_psi_smoothing_bound (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x) (hX : max (836 / 100 : ℝ) (8 / R) < X R x) :
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧
      |Chebyshev.psi x - x| < x * Real.sqrt (8 / Real.pi) * Real.sqrt (X R x) * Real.exp (-X R x) *
        (Real.sqrt (Real.sqrt (U (X R x) ν)) *
          Real.exp ((591 / 100 : ℝ) * Real.sqrt (X R x) * Real.exp (-X R x))) := by
  have hf := threshold_facts R x hR hX
  obtain ⟨ν, hν, hν1, hseed, hk⟩ := exists_optimal_smoothing_parameter (X R x) hf.1
  refine ⟨ν, hν, hν1, ?_⟩
  let δ := optimalWidth (X R x) ν
  let b := Real.sqrt (X R x) * Real.exp (-X R x)
  have hδ : 0 < δ := optimalWidth_pos (X R x) ν hf.1 hν
  have hb : 0 < b := mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.exp_pos _)
  have hδb : δ ≤ (4 / 5 : ℝ) * b := by
    have h := optimalWidth_le_four_fifths (X R x) ν hf.1 hν hν1.le hk
    dsimp [δ, b]
    linarith
  have hbase : 1 ≤ x - 2 * (δ * x) := smoothing_lower_base_ge_one R x ν hR hx hX hν hν1.le hk
  have hx1 : 1 < x := by rw [← Real.exp_log hx]; exact Real.one_lt_exp_iff.mpr hf.2.1
  have hu := double_average_resampling_error R x ν x hR hx hzero hX hν hν1.le hseed.le hk hx1.le
    (by nlinarith)
  have hl := double_average_resampling_error R x ν (x - 2 * (δ * x)) hR hx hzero hX hν hν1.le hseed.le hk hbase
    (by dsimp [δ]; nlinarith [mul_pos hδ hx])
  change |doubleBoxAverage Chebyshev.psi x (δ * x) - (x + δ * x)| < δ * x * ((1 + 2 * δ)^3 + b) at hu
  change |doubleBoxAverage Chebyshev.psi (x - 2 * (δ * x)) (δ * x) - (x - 2 * (δ * x) + δ * x)| <
      δ * x * ((1 + 2 * δ)^3 + b) at hl
  have he : x - 2 * (δ * x) + δ * x = x - δ * x := by ring
  rw [he] at hl
  have hψ := psi_error_of_double_average_errors_strict x (δ * x) (δ * x * ((1 + 2 * δ)^3 + b))
    (mul_pos hδ hx) hl hu
  have he' : δ * x * ((1 + 2 * δ)^3 + b) + δ * x = δ * x * ((1 + 2 * δ)^3 + b + 1) := by ring
  rw [he'] at hψ
  have hnum := mul_lt_mul_of_pos_left (final_smoothing_exponential_bound δ b hδ hb hδb) (mul_pos hδ hx)
  have htarget := mul_le_mul_of_nonneg_right
    (optimalWidth_fourth_root_bound (X R x) ν hf.1 hν hν1.le hk)
    (by positivity : 0 ≤ x * Real.exp ((591 / 100 : ℝ) * b))
  apply hψ.trans (hnum.trans_le _)
  convert htarget using 1 <;> first | rfl | (dsimp [δ, b]; ring)

end DusartSmoothing


