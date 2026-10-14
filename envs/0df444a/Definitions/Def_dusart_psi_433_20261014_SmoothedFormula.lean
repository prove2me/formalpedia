-- Prove2me | Definitions.Def_dusart_psi_433_20261014_SmoothedFormula
-- name    : dusart_psi_433_20261014_SmoothedFormula
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T10:03:00.125878+00:00
-- url     : https://prove2.me/theorems/4795b2cf-5191-4729-b8b6-22066363f3dd
-- title:
--   Dusart smoothing: Smoothed Formula
-- statement:
--   This module gives the complete smoothed formula component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_KernelSmoothing
import Definitions.Def_dusart_psi_433_20261014_ZetaZeroConstant
import Definitions.Def_dusart_psi_433_20261014_IntegratedPsi
noncomputable section
namespace DusartSmoothing
open Complex Real MeasureTheory

noncomputable def smoothedZeroKernel (x h : ℝ) (ρ : ℂ) : ℂ :=
  (quadraticKernel (x + 2 * h) ρ - 2 * quadraticKernel (x + h) ρ + quadraticKernel x ρ) /
    (h : ℂ)^2

lemma smoothed_zero_series_summable (x h : ℝ) (hx : 1 ≤ x) (hh : 0 < h) :
    Summable (fun ρ : NontrivialZetaZero => (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val) := by
  have h0 := actual_quadratic_zero_series_summable x hx
  have h1 := actual_quadratic_zero_series_summable (x + h) (by linarith)
  have h2 := actual_quadratic_zero_series_summable (x + 2 * h) (by linarith)
  have hs := ((h2.sub (h1.mul_left 2)).add h0).div_const ((h : ℂ)^2)
  apply hs.congr
  intro ρ
  dsimp [smoothedZeroKernel]
  ring

lemma smoothed_zero_series_eq (x h : ℝ) (hx : 1 ≤ x) (hh : 0 < h) :
    (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val) =
      ((∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel (x + 2 * h) ρ.val) -
       2 * (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel (x + h) ρ.val) +
       (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val)) / (h : ℂ)^2 := by
  have h0 := actual_quadratic_zero_series_summable x hx
  have h1 := actual_quadratic_zero_series_summable (x + h) (by linarith)
  have h2 := actual_quadratic_zero_series_summable (x + 2 * h) (by linarith)
  have he : (fun ρ : NontrivialZetaZero => (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val) =
      fun ρ => ((RvM.zeroMult ρ.val : ℂ) * quadraticKernel (x + 2 * h) ρ.val -
        2 * ((RvM.zeroMult ρ.val : ℂ) * quadraticKernel (x + h) ρ.val) +
        (RvM.zeroMult ρ.val : ℂ) * quadraticKernel x ρ.val) / (h : ℂ)^2 := by
    funext ρ; dsimp [smoothedZeroKernel]; ring
  rw [he, tsum_div_const, (h2.sub (h1.mul_left 2)).tsum_add h0,
    h2.tsum_sub (h1.mul_left 2), tsum_mul_left]

lemma doubleBoxAverage_psi_explicit_formula (N : ℕ) (x h : ℝ)
    (hx : 1 ≤ x) (hh : 0 < h) (hN : x + 2 * h ≤ N) :
    (doubleBoxAverage Chebyshev.psi x h : ℂ) = ((x + h : ℝ) : ℂ) - logDeriv riemannZeta 0 -
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel x h ρ.val) +
      (perronLeftRemainder (x + 2 * h) - 2 * perronLeftRemainder (x + h) +
        perronLeftRemainder x) / (h : ℂ)^2 := by
  have h0N : x ≤ N := by linarith
  have h1N : x + h ≤ N := by linarith
  have h0x : 0 ≤ x := by linarith
  have hψ : (doubleBoxAverage Chebyshev.psi x h : ℂ) =
      ((secondPsiPrimitive N (x + 2 * h) : ℂ) - 2 * (secondPsiPrimitive N (x + h) : ℂ) +
        (secondPsiPrimitive N x : ℂ)) / (h : ℂ)^2 := by
    rw [doubleBoxAverage_psi_eq_second_difference N x h h0x hh hN]
    push_cast
    rfl
  rw [hψ, smoothed_zero_series_eq x h hx hh,
    secondPsiPrimitive_explicit_formula N (x + 2 * h) (by linarith) hN,
    secondPsiPrimitive_explicit_formula N (x + h) (by linarith) h1N,
    secondPsiPrimitive_explicit_formula N x hx h0N]
  push_cast
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  field_simp [hhC]
  ring

lemma norm_smoothed_perron_remainder (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    ‖(perronLeftRemainder (x + 2 * h) - 2 * perronLeftRemainder (x + h) +
      perronLeftRemainder x) / (h : ℂ)^2‖ ≤
      512 * (x + 2 * h) ^ (3 / 2 : ℝ) / h^2 := by
  have h0 := norm_perronLeftRemainder x hx
  have h1 := norm_perronLeftRemainder (x + h) (by linarith)
  have h2 := norm_perronLeftRemainder (x + 2 * h) (by linarith)
  have hp0 : x ^ (3 / 2 : ℝ) ≤ (x + 2 * h) ^ (3 / 2 : ℝ) := by gcongr <;> linarith
  have hp1 : (x + h) ^ (3 / 2 : ℝ) ≤ (x + 2 * h) ^ (3 / 2 : ℝ) := by gcongr <;> linarith
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  have hn := (norm_add_le
    (perronLeftRemainder (x + 2 * h) - 2 * perronLeftRemainder (x + h)) (perronLeftRemainder x)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  norm_num [norm_mul] at hn
  nlinarith

end DusartSmoothing


