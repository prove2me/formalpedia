-- Prove2me | Definitions.Def_dusart_psi_433_20261014_KernelSmoothing
-- name    : dusart_psi_433_20261014_KernelSmoothing
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:59:19.675351+00:00
-- url     : https://prove2.me/theorems/b4ee7233-9f65-45de-b389-af6357a9cfe9
-- title:
--   Dusart smoothing: Kernel Smoothing
-- statement:
--   This module gives the complete kernel smoothing component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

lemma integral_shift_cpow (x h : ℝ) (r : ℂ) (hr : -1 < r.re) :
    (∫ u in (0 : ℝ)..h, ((x + u : ℝ) : ℂ)^r) =
      (((x + h : ℝ) : ℂ)^(r + 1) - (x : ℂ)^(r + 1)) / (r + 1) := by
  rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => (y : ℂ)^r) x]
  simp only [add_zero]
  exact integral_cpow (Or.inl hr)

lemma quadraticKernel_second_difference_integral (x h : ℝ) (ρ : ℂ) (hρ : 0 < ρ.re) :
    quadraticKernel (x + 2 * h) ρ - 2 * quadraticKernel (x + h) ρ + quadraticKernel x ρ =
      ∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, ((x + u + v : ℝ) : ℂ)^ρ / ρ := by
  have h0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have h1 : ρ + 1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have h2 : ρ + 2 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have he : (fun u : ℝ => ∫ v in (0 : ℝ)..h, ((x + u + v : ℝ) : ℂ)^ρ / ρ) =
      fun u => ((((x + h + u : ℝ) : ℂ)^(ρ + 1) -
        ((x + u : ℝ) : ℂ)^(ρ + 1)) / (ρ + 1)) / ρ := by
    funext u
    rw [intervalIntegral.integral_div, integral_shift_cpow (x + u) h ρ (by linarith)]
    congr 3
    congr 1
    ring
  have hi0 : IntervalIntegrable (fun u : ℝ => ((x + u : ℝ) : ℂ)^(ρ + 1)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal_cpow_const (by simp; linarith : 0 < (ρ + 1).re)).comp (by fun_prop)
  have hi1 : IntervalIntegrable (fun u : ℝ => ((x + h + u : ℝ) : ℂ)^(ρ + 1)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal_cpow_const (by simp; linarith : 0 < (ρ + 1).re)).comp (by fun_prop)
  rw [he, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_sub hi1 hi0,
    integral_shift_cpow (x + h) h (ρ + 1) (by simp; linarith),
    integral_shift_cpow x h (ρ + 1) (by simp; linarith)]
  rw [show x + h + h = x + 2 * h by ring, show ρ + 1 + 1 = ρ + 2 by ring]
  unfold quadraticKernel
  field_simp
  ring

lemma norm_quadraticKernel_second_difference_low (x h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (ρ : ℂ) (hρ : 0 < ρ.re) (hi : 0 < |ρ.im|)
    (hp : ∀ y ∈ Set.Icc x (x + 2 * h), ‖(y : ℂ)^ρ‖ ≤ M) :
    ‖quadraticKernel (x + 2 * h) ρ - 2 * quadraticKernel (x + h) ρ + quadraticKernel x ρ‖ ≤
      h^2 * M / |ρ.im| := by
  rw [quadraticKernel_second_difference_integral x h ρ hρ]
  have hnρ : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hinner : ∀ u ∈ Set.uIoc (0 : ℝ) h,
      ‖∫ v in (0 : ℝ)..h, ((x + u + v : ℝ) : ℂ)^ρ / ρ‖ ≤ M / |ρ.im| * h := by
    intro u hu
    rw [Set.uIoc_of_le hh.le] at hu
    have hb : ∀ v ∈ Set.uIoc (0 : ℝ) h, ‖((x + u + v : ℝ) : ℂ)^ρ / ρ‖ ≤ M / |ρ.im| := by
      intro v hv
      rw [Set.uIoc_of_le hh.le] at hv
      rw [norm_div]
      exact div_le_div₀ hM (hp _ ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩)
        hi hnρ
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [sub_zero, abs_of_pos hh] using hb'
  have hh' := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  rw [sub_zero, abs_of_pos hh] at hh'
  exact hh'.trans_eq (by ring)

end DusartSmoothing


