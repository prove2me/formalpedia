-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ReflectedPowers
-- name    : dusart_psi_433_20261014_ReflectedPowers
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:32:26.612409+00:00
-- url     : https://prove2.me/theorems/5681e68d-68a6-4dca-ae7e-b5102bb8e8b4
-- title:
--   Dusart smoothing: Reflected Powers
-- statement:
--   This module gives the complete reflected powers component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroReflection
import Definitions.Def_dusart_psi_433_20261014_Parameters
noncomputable section
namespace DusartSmoothing
open Complex Real

lemma reflected_zero_power_majorant (R x : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (ρ : ℂ) (hρ : RvM.IsNontrivialZero ρ) :
    ‖(x : ℂ)^ρ‖ / x + ‖(x : ℂ)^(1 - starRingEnd ℂ ρ)‖ / x ≤
      Real.exp (-(X R x)^2 / Real.log |ρ.im|) + Real.sqrt (1 / x) := by
  let τ : ℂ := 1 - starRingEnd ℂ ρ
  have hτ := RvM.nontrivial_zero_reflect hρ
  have hxp : 0 < x := by linarith
  have ht := RvM.nontrivial_zero_abs_height ρ hρ
  have hτim : |τ.im| = |ρ.im| := by simp [τ]
  let p := ‖(x : ℂ)^ρ‖ / x
  let q := ‖(x : ℂ)^τ‖ / x
  let U := Real.exp (-(X R x)^2 / Real.log |ρ.im|)
  let S := Real.sqrt (1 / x)
  have hp : p ≤ U := zero_power_majorant R x hR hxp hx hzero ρ hρ.1 ht
  have hq : q ≤ U := by
    have h := zero_power_majorant R x hR hxp hx hzero τ hτ.1 (by rw [hτim]; exact ht)
    simpa only [hτim] using h
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hU : 0 < U := Real.exp_pos _
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S^2 = 1 / x := Real.sq_sqrt (by positivity)
  have hpq : p * q = 1 / x := by
    dsimp [p, q]
    rw [norm_cpow_eq_rpow_re_of_pos hxp, norm_cpow_eq_rpow_re_of_pos hxp,
      div_mul_div_comm, ← Real.rpow_add hxp]
    have he : ρ.re + τ.re = 1 := by simp [τ]
    rw [he, Real.rpow_one]
    field_simp
  have hproduct : p * q ≤ U^2 := by
    simpa only [pow_two] using mul_le_mul hp hq hq0 hU.le
  have hSU : S ≤ U := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)
  have hs := mul_nonneg hS (sub_nonneg.mpr hSU)
  change p + q ≤ U + S
  nlinarith

end DusartSmoothing


