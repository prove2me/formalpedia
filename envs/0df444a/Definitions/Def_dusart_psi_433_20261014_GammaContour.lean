-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaContour
-- name    : dusart_psi_433_20261014_GammaContour
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:25:15.503866+00:00
-- url     : https://prove2.me/theorems/470d23ac-74b5-4784-9e26-a60189370f98
-- title:
--   Dusart smoothing: Gamma Contour
-- statement:
--   This module gives the complete gamma contour component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ContourSymmetry
import Definitions.Def_dusart_psi_433_20261014_GammaDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
Adapted from accepted gamma-contour proofs on Prove2Me. -/
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set MeasureTheory
open scoped Interval
def gammaRightHalfPlane : Set ℂ := {s | 0 < s.re}

lemma isOpen_gammaRightHalfPlane : IsOpen gammaRightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

lemma Gamma_half_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
  apply Complex.differentiableAt_Gamma
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma Gammaℝ_differentiableOn : DifferentiableOn ℂ Complex.Gammaℝ gammaRightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  have : Complex.Gammaℝ = fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  rw [this]
  exact h1.mul h2

lemma Gammaℝ_analyticOnNhd : AnalyticOnNhd ℂ Complex.Gammaℝ gammaRightHalfPlane :=
  Gammaℝ_differentiableOn.analyticOnNhd isOpen_gammaRightHalfPlane

/-- logDeriv Γℝ is holomorphic on Re s > 0. -/
lemma logDeriv_Gammaℝ_differentiableOn : DifferentiableOn ℂ (logDeriv Complex.Gammaℝ) gammaRightHalfPlane := by
  have hA := Gammaℝ_analyticOnNhd
  have hd : DifferentiableOn ℂ (deriv Complex.Gammaℝ) gammaRightHalfPlane := hA.deriv.differentiableOn
  have : logDeriv Complex.Gammaℝ = fun s => deriv Complex.Gammaℝ s / Complex.Gammaℝ s := by
    funext s; rfl
  rw [this]
  exact hd.div hA.differentiableOn fun s hs => Complex.Gammaℝ_ne_zero_of_re_pos hs



theorem logDeriv_GammaR {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hf : (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, hπ, false_and, not_false_eq_true]
  have hg : (fun s : ℂ => Complex.Gamma (s / 2)) s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := fun s : ℂ => Complex.Gamma (s / 2)) s hf hg hdf hdg]
  -- first factor
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
      have : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).neg.div_const (2:ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply, hder.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  -- second factor
  have h2 : logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) s = (1/2 : ℂ) * Complex.digamma (s / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s)
      (Gamma_half_differentiableAt hs) (by fun_prop)
    rw [show (Complex.Gamma ∘ fun s : ℂ => s / 2) = fun s => Complex.Gamma (s / 2) from rfl] at this
    rw [this, Complex.digamma_def]
    have : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]

/-- on the critical line: Re(logDeriv Γℝ(½+it)) = π·μ(t). -/
theorem re_logDeriv_Gammaℝ_half (t : ℝ) :
    (logDeriv Complex.Gammaℝ (1/2 + t * I)).re = Real.pi * gammaDensity t := by
  rw [logDeriv_GammaR (by simp)]
  have : ((1:ℂ)/2 + t * I) / 2 = 1 / 4 + Complex.I * t / 2 := by ring
  rw [this, gammaDensity]
  simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re,
    Complex.one_re]
  have hπ := Real.pi_ne_zero
  field_simp
  simp
  ring



theorem gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, gammaDensity t := by
  set F := logDeriv Complex.Gammaℝ with hF
  -- Cauchy–Goursat on the rectangle [1/2, 2] × [T₁, T₂]
  have hrect : (Set.uIcc (1/2:ℝ) 2 ×ℂ Set.uIcc T₁ T₂) ⊆ gammaRightHalfPlane := by
    rintro s ⟨hre, -⟩
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hre
    show 0 < s.re
    have := hre.1
    linarith [this]
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (1/2 + T₁ * I) (2 + T₂ * I)
    (logDeriv_Gammaℝ_differentiableOn.mono (by simpa using hrect))
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, one_im, mul_im, zero_add, div_ofNat_re, div_ofNat_im, zero_div,
    re_ofNat, im_ofNat] at hCG
  have hhc : halfContour F T₁ T₂ = I * ∫ y : ℝ in T₁..T₂, F (1/2 + y * I) := by
    unfold halfContour
    have hthis := hCG
    simp only [smul_eq_mul] at hthis
    have hc : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
    simp only [hc] at hthis
    -- bottom - top + I*right - I*left = 0
    linear_combination hthis
  rw [hhc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  -- Re ∫ = ∫ Re
  have hcont : Continuous fun y : ℝ => F (1/2 + y * I) := by
    have hd := logDeriv_Gammaℝ_differentiableOn
    have : Continuous fun y : ℝ => ((1:ℂ)/2 + y * I) := by fun_prop
    refine (hd.continuousOn.comp_continuous this fun y => ?_)
    show 0 < ((1:ℂ)/2 + y * I).re
    simp
  rw [show ((∫ y : ℝ in T₁..T₂, F (1/2 + y * I)).re) = ∫ y : ℝ in T₁..T₂, (F (1/2 + y * I)).re from
    (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)).symm]
  simp_rw [hF, re_logDeriv_Gammaℝ_half]
  rw [intervalIntegral.integral_const_mul]
  field_simp

end DusartSmoothing.RvM


