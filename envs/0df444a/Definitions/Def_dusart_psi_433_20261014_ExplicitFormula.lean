-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ExplicitFormula
-- name    : dusart_psi_433_20261014_ExplicitFormula
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:57:36.875665+00:00
-- url     : https://prove2.me/theorems/d8d2b023-108b-4e02-83d9-a1344fff2f5a
-- title:
--   Dusart smoothing: Explicit Formula
-- statement:
--   This module gives the complete explicit formula component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_HorizontalLimits
noncomputable section
namespace DusartSmoothing
open Complex Real Set Filter Topology MeasureTheory
open DusartSmoothing.Contour

noncomputable def perronLeftRemainder (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I)

lemma norm_perronLeftRemainder (x : ℝ) (hx : 0 < x) :
    ‖perronLeftRemainder x‖ ≤ 128 * x ^ (3 / 2 : ℝ) := by
  have h := norm_perron_left_integral x hx
  rw [perronLeftRemainder, norm_mul]
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    norm_num [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]
  calc _ ≤ 1 / (2 * Real.pi) * (256 * Real.pi * x ^ (3 / 2 : ℝ)) := by gcongr
    _ = 128 * x ^ (3 / 2 : ℝ) := by field_simp; ring

/-- An infinite explicit formula for the actual second Chebyshev primitive,
with the actual zeta zeros and a quantified left-line remainder. -/
theorem secondPsiPrimitive_explicit_formula (N : ℕ) (x : ℝ) (hx : 1 ≤ x) (hN : x ≤ N) :
    (secondPsiPrimitive N x : ℂ) = (x : ℂ)^3 / 6 - (x : ℂ)^2 / 2 * logDeriv riemannZeta 0 -
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val) +
      perronLeftRemainder x := by
  have hxp : 0 < x := by linarith
  obtain ⟨R, hRt, hgood, hbot, htop⟩ := exists_perron_good_heights x hx
  let J : ℕ → ℂ := fun j => RectangleIntegral' (perronIntegrand x)
    (-(1 / 2 : ℂ) - R j * I) (2 + R j * I)
  have he : J = fun j => (1 / (2 * Real.pi * I) : ℂ) *
      ((∫ σ in (-(1 / 2) : ℝ)..2, perronIntegrand x (σ + (-R j) * I)) -
       (∫ σ in (-(1 / 2) : ℝ)..2, perronIntegrand x (σ + R j * I)) +
       I * (∫ t in -R j..R j, perronIntegrand x (2 + t * I)) -
       I * (∫ t in -R j..R j, perronIntegrand x (-(1 / 2 : ℂ) + t * I))) := by
    funext j
    norm_num [J, RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] <;> ring
  have hl : Tendsto J atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) *
      ((∫ t : ℝ, perronIntegrand x (2 + t * I)) -
       (∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I))))) := by
    rw [he]
    have h := (((hbot.sub htop).add ((perron_right_vertical_tendsto x hxp hRt).const_mul I)).sub
      ((perron_left_vertical_tendsto x hxp hRt).const_mul I)).const_mul (1 / (2 * Real.pi * I) : ℂ)
    have hc : (1 / (2 * Real.pi * I) : ℂ) *
        (0 - 0 + I * (∫ t : ℝ, perronIntegrand x (2 + t * I)) -
         I * (∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I))) =
        (1 / (2 * Real.pi) : ℂ) *
        ((∫ t : ℝ, perronIntegrand x (2 + t * I)) -
         (∫ t : ℝ, perronIntegrand x (-(1 / 2 : ℂ) + t * I))) := by
      field_simp
      ring
    rw [hc] at h
    exact h
  have hzeros := actual_quadratic_zero_window_sum_tendsto x hx hRt
  have hr : Tendsto (fun j => (x : ℂ)^3 / 6 - (x : ℂ)^2 / 2 * logDeriv riemannZeta 0 -
      ∑ ρ ∈ (RvM.finite_symmetric_zero_window (R j)).toFinset,
        (RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ) atTop
      (𝓝 ((x : ℂ)^3 / 6 - (x : ℂ)^2 / 2 * logDeriv riemannZeta 0 -
        ∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val)) :=
    tendsto_const_nhds.sub hzeros
  have he2 : J = fun j => (x : ℂ)^3 / 6 - (x : ℂ)^2 / 2 * logDeriv riemannZeta 0 -
      ∑ ρ ∈ (RvM.finite_symmetric_zero_window (R j)).toFinset,
        (RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ := by
    funext j
    exact perron_finite_rectangle x hxp (R j) (hgood j).1 (hgood j).2
  rw [← he2] at hr
  have hEq := tendsto_nhds_unique hl hr
  rw [secondPsiPrimitive_perron_kernel N x hxp hN]
  unfold perronLeftRemainder
  linear_combination hEq

end DusartSmoothing


