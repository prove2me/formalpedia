-- Prove2me | Definitions.Def_dusart_psi_433_20261014_WindowPowers
-- name    : dusart_psi_433_20261014_WindowPowers
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:48:36.177988+00:00
-- url     : https://prove2.me/theorems/78a20014-4365-462e-8ea1-2e3645ce3468
-- title:
--   Dusart smoothing: Window Powers
-- statement:
--   This module gives the complete window powers component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GaussianWindow
import Definitions.Def_dusart_psi_433_20261014_FiniteReflection
noncomputable section
namespace DusartSmoothing
open Real Complex

lemma sqrt_inverse_le_gaussian_remainder (X x : ℝ) (hx : 0 < x)
    (hlog : 8 * X < Real.log x) : Real.sqrt (1 / x) ≤ Real.exp (-4 * X) := by
  have he : Real.sqrt (1 / x) = Real.exp (-Real.log x / 2) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / x)
    have hp : Real.exp (-Real.log x / 2)^2 = 1 / x := by
      rw [← Real.exp_nat_mul]
      have hh : (2 : ℕ) * (-Real.log x / 2) = -Real.log x := by norm_num <;> ring
      rw [hh, Real.exp_neg, Real.exp_log hx, one_div]
    nlinarith [Real.sqrt_nonneg (1 / x), Real.exp_pos (-Real.log x / 2)]
  rw [he]
  exact Real.exp_le_exp.mpr (by linarith)

lemma positive_window_power_weight_bound (R x ν B : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed (X R x) ≤ ν)
    (hk : k (X R x) ν = 1) (hB : transformHeight (X R x) ν ≤ B) :
    2 * (∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth (X R x) ν) (transformHeight (X R x) ν) ρ.im *
        (‖(x : ℂ)^ρ‖ / x)) < optimalWidth (X R x) ν := by
  have hf := threshold_facts R x hR hX
  have hq := sqrt_inverse_le_gaussian_remainder (X R x) x (by linarith) hf.2.2.2
  have hwin := reflected_gaussian_window_bound (X R x) ν B (Real.sqrt (1 / x))
    hf.1 hν hν1 hseed hk hB (Real.sqrt_nonneg _) hq
  have hr := finite_reflected_zero_power_sum R x hR hx hzero
    (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset
    (fun ρ hρ => by rw [Set.Finite.mem_toFinset] at hρ; exact hρ.1)
    (fun ρ hρ => zero_window_reflection (by norm_num) ρ hρ)
    (resamplingZeroWeight (optimalWidth (X R x) ν) (transformHeight (X R x) ν))
    (fun ρ hρ => resamplingZeroWeight_nonneg _ _ _ (by
      have hh := hρ
      rw [Set.Finite.mem_toFinset] at hh
      have hh := hh.2.1
      linarith))
  have he : (∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth (X R x) ν) (transformHeight (X R x) ν) ρ.im *
        Real.exp (-(X R x)^2 / Real.log |ρ.im|)) =
      ∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth (X R x) ν) (transformHeight (X R x) ν) ρ.im *
        Real.exp (-(X R x)^2 / Real.log ρ.im) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [abs_of_pos (show 0 < ρ.im by rw [Set.Finite.mem_toFinset] at hρ; linarith [hρ.2.1])]
  rw [he] at hr
  exact hr.trans_lt hwin

end DusartSmoothing


