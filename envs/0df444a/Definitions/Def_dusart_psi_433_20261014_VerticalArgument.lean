-- Prove2me | Definitions.Def_dusart_psi_433_20261014_VerticalArgument
-- name    : dusart_psi_433_20261014_VerticalArgument
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:18:56.558529+00:00
-- url     : https://prove2.me/theorems/ac7b7f2b-eee3-4b60-a06e-4d7a8c966541
-- title:
--   Dusart smoothing: Vertical Argument
-- statement:
--   This module gives the complete vertical argument component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZetaCenter
/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
Adapted from the accepted vertical argument bound on Prove2Me. -/
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set MeasureTheory Real intervalIntegral

lemma pi_sq_div_six_sub_one_lt_one : Real.pi ^ 2 / 6 - 1 < 1 := by
  have := Real.pi_lt_d2  -- π < 3.15
  nlinarith [Real.pi_pos]








lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re := by
  have h := norm_riemannZeta_sub_one_le (s := 2 + t * I) (by simp)
  have h2 : |(riemannZeta (2 + t * I) - 1).re| ≤ ‖riemannZeta (2 + t * I) - 1‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := (abs_le.mp (h2.trans h)).1
  linarith [pi_sq_div_six_sub_one_lt_one]

lemma two_add_mul_I_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this


/-- Continuity of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) := by
  have hγ : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  have hd : Continuous (fun t : ℝ => deriv riemannZeta (2 + t * I)) :=
    hA.deriv.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hz : Continuous (fun t : ℝ => riemannZeta (2 + t * I)) :=
    hA.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hne : ∀ t : ℝ, riemannZeta (2 + t * I) ≠ 0 := fun t h => by
    have := re_riemannZeta_two_pos t; rw [h] at this; simp at this
  simp only [logDeriv_apply]
  exact ((hd.div hz hne).mul continuous_const)




lemma hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (riemannZeta (2 + u * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t := by
  have hζ := (differentiableAt_riemannZeta (two_add_mul_I_ne_one t)).hasDerivAt
  have hpath : HasDerivAt (fun u : ℝ => (2 : ℂ) + u * I) I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (2 : ℂ)
  have hslit : riemannZeta (2 + t * I) ∈ Complex.slitPlane :=
    by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (re_riemannZeta_two_pos t)
  have h := (Complex.hasDerivAt_log hslit).comp t (hζ.comp t hpath)
  convert h using 1
  all_goals first | rfl | (simp only [logDeriv_apply]; ring)

theorem vertical_two : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := by
  intro T₁ T₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_log_riemannZeta_two t)
    (continuous_logDeriv_riemannZeta_two.intervalIntegrable _ _)]
  rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 : |(riemannZeta (2 + T₂ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₂).le
  have h2 : |(riemannZeta (2 + T₁ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₁).le
  calc |(riemannZeta (2 + T₂ * I)).arg - (riemannZeta (2 + T₁ * I)).arg|
      ≤ |(riemannZeta (2 + T₂ * I)).arg| + |(riemannZeta (2 + T₁ * I)).arg| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring

end DusartSmoothing.RvM


