-- Prove2me | Definitions.Def_dusart_psi_433_20261014_CoefficientBounds
-- name    : dusart_psi_433_20261014_CoefficientBounds
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T10:05:22.659366+00:00
-- url     : https://prove2.me/theorems/195fa374-05b9-4de3-ac5b-9c2ad0a4c75a
-- title:
--   Dusart smoothing: Coefficient Bounds
-- statement:
--   This module gives the complete coefficient bounds component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_SmoothedFormula
noncomputable section
namespace DusartSmoothing
open Complex Real Set

lemma norm_smoothedZeroKernel_low (x h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (ρ : ℂ) (hρ : 0 < ρ.re) (hi : 0 < |ρ.im|)
    (hp : ∀ y ∈ Set.Icc x (x + 2 * h), ‖(y : ℂ)^ρ‖ ≤ M) :
    ‖smoothedZeroKernel x h ρ‖ ≤ M / |ρ.im| := by
  have hb := norm_quadraticKernel_second_difference_low x h M hh hM ρ hρ hi hp
  rw [smoothedZeroKernel, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ (h^2 * M / |ρ.im|) / h^2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ = M / |ρ.im| := by field_simp [hh.ne']

lemma norm_quadraticKernel_on_smoothing_interval (x h M : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hM : 0 ≤ M) (ρ : ℂ) (hi : 0 < |ρ.im|)
    (hp : ∀ y ∈ Set.Icc x (x + 2 * h), ‖(y : ℂ)^ρ‖ ≤ M)
    (y : ℝ) (hy : y ∈ Set.Icc x (x + 2 * h)) :
    ‖quadraticKernel y ρ‖ ≤ M * (x + 2 * h)^2 / |ρ.im|^3 := by
  have hyp : 0 < y := hx.trans_le hy.1
  have hn := norm_quadraticKernel_le_height y hyp hi
  have he : y ^ (ρ.re + 2) = ‖(y : ℂ)^ρ‖ * y^2 := by
    rw [Real.rpow_add hyp, Real.rpow_two, norm_cpow_eq_rpow_re_of_pos hyp]
  rw [he] at hn
  exact hn.trans (by gcongr; exact hp y hy; exact hy.2)

lemma norm_smoothedZeroKernel_high (x h M : ℝ) (hx : 0 < x) (hh : 0 < h) (hM : 0 ≤ M)
    (ρ : ℂ) (hi : 0 < |ρ.im|)
    (hp : ∀ y ∈ Set.Icc x (x + 2 * h), ‖(y : ℂ)^ρ‖ ≤ M) :
    ‖smoothedZeroKernel x h ρ‖ ≤ 4 * M * (x + 2 * h)^2 / (h^2 * |ρ.im|^3) := by
  have h0 := norm_quadraticKernel_on_smoothing_interval x h M hx hh hM ρ hi hp x ⟨le_rfl, by linarith⟩
  have h1 := norm_quadraticKernel_on_smoothing_interval x h M hx hh hM ρ hi hp (x + h)
    ⟨by linarith, by linarith⟩
  have h2 := norm_quadraticKernel_on_smoothing_interval x h M hx hh hM ρ hi hp (x + 2 * h)
    ⟨by linarith, le_rfl⟩
  rw [smoothedZeroKernel, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hn := (norm_add_le
    (quadraticKernel (x + 2 * h) ρ - 2 * quadraticKernel (x + h) ρ) (quadraticKernel x ρ)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  norm_num [norm_mul] at hn
  calc
    _ ≤ (4 * M * (x + 2 * h)^2 / |ρ.im|^3) / h^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [show 4 * M * (x + 2 * h)^2 / |ρ.im|^3 =
        4 * (M * (x + 2 * h)^2 / |ρ.im|^3) by ring]
      linarith
    _ = _ := by ring

end DusartSmoothing


