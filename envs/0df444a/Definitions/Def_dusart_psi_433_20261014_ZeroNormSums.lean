-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroNormSums
-- name    : dusart_psi_433_20261014_ZeroNormSums
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:38:26.257544+00:00
-- url     : https://prove2.me/theorems/c4753550-023c-4994-90fa-92b5298efd37
-- title:
--   Dusart smoothing: Zero Norm Sums
-- statement:
--   This module gives the complete zero norm sums component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PositiveZeroSeries
import Definitions.Def_dusart_psi_433_20261014_PerronResidues
noncomputable section
namespace DusartSmoothing
open Complex Set

lemma weighted_quadratic_zero_norm_le (x : ℝ) (hx : 1 ≤ x) (ρ : ℂ)
    (hρ : RvM.IsNontrivialZero ρ) (hγ : 0 < ρ.im) :
    ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖ ≤
      x^3 * ((RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) := by
  have hxp : 0 < x := by linarith
  rw [quadraticKernel_eq_mellin x hxp ρ hρ.2.1, norm_mul, Complex.norm_natCast]
  have hMF := norm_quadratic_mellin_le x hxp ρ hρ.2.1 hγ.ne'
  rw [abs_of_pos hγ] at hMF
  have hp : x ^ (ρ.re + 2) ≤ x^3 := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (show ρ.re + 2 ≤ (3 : ℝ) by linarith [hρ.2.2])
    simpa using h
  calc (RvM.zeroMult ρ : ℝ) * ‖mellin (quadraticPrimeWeight x) ρ‖
      ≤ (RvM.zeroMult ρ : ℝ) * (x^3 / ρ.im^3) :=
        mul_le_mul_of_nonneg_left (hMF.trans (div_le_div_of_nonneg_right hp (by positivity)))
          (Nat.cast_nonneg _)
    _ = _ := by ring

lemma finite_positive_quadratic_norm_sum_bound (x : ℝ) (hx : 1 ≤ x) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖) ≤ 12 * x^3 := by
  calc (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ‖)
      ≤ ∑ ρ ∈ Z, x^3 * ((RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact weighted_quadratic_zero_norm_le x hx ρ (hZ ρ hρ).1 (hZ ρ hρ).2
    _ = x^3 * (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) := by rw [Finset.mul_sum]
    _ ≤ 12 * x^3 := by
      have h := mul_le_mul_of_nonneg_left (finite_positive_inverse_cube_bound Z hZ)
        (by positivity : (0 : ℝ) ≤ x^3)
      simpa [mul_comm] using h

end DusartSmoothing


