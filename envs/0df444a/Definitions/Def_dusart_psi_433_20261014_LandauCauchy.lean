-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LandauCauchy
-- name    : dusart_psi_433_20261014_LandauCauchy
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:19.819267+00:00
-- url     : https://prove2.me/theorems/3c80f422-c3a0-4db9-b8e4-07fb5394f2d6
-- title:
--   Dusart smoothing: Landau Cauchy
-- statement:
--   This module gives the complete landau cauchy component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LandauDefs
import Mathlib.Analysis.Complex.Liouville

noncomputable section
namespace DusartSmoothing.Landau
open Complex Real Set Metric

lemma BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hM : 0 < M) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOn ℂ f (Metric.ball 0 R)) (h0 : f 0 = 0)
    (hRe : ∀ w ∈ Metric.ball 0 R, (f w).re ≤ M)
    (hz : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  let ρ : ℝ := (R - r) / 2
  let r' : ℝ := (R + r) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hr' : 0 < r' := by dsimp [r']; linarith
  have hr'R : r' < R := by dsimp [r']; linarith
  have hzn : ‖z‖ ≤ r := by simpa using hz
  have hsub : Metric.closedBall z ρ ⊆ Metric.ball (0 : ℂ) R := by
    intro w hw
    have hwn : ‖w - z‖ ≤ ρ := by simpa [Complex.dist_eq] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [ρ] at hwn
    linarith
  have hd : DiffContOnCl ℂ f (Metric.ball z ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hρ.ne']
    exact hf.differentiableOn.mono hsub
  have hC : ∀ w ∈ Metric.sphere z ρ, ‖f w‖ ≤ 2 * M * r' / (R - r') := by
    intro w hw
    have hwn : ‖w - z‖ = ρ := by simpa [Complex.dist_eq] using hw
    have hw' : ‖w‖ ≤ r' := by
      have hn := norm_le_norm_sub_add w z
      rw [hwn] at hn
      dsimp [ρ, r'] at hn ⊢
      linarith
    have hwR : w ∈ Metric.ball (0 : ℂ) R := by simpa using hw'.trans_lt hr'R
    have hb := Complex.borelCaratheodory_zero hM hf.differentiableOn hRe
      (hr.trans hrR) hwR h0
    exact hb.trans (by gcongr)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  have he : (2 * M * r' / (R - r')) / ρ = 4 * M * (R + r) / (R - r)^2 := by
    dsimp [ρ, r']
    field_simp
    ring
  rw [he] at hc
  have hden : 0 < R - r := by linarith
  refine hc.trans ?_
  calc
    4 * M * (R + r) / (R - r)^2 ≤ 8 * M * R / (R - r)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    _ = 8 * M * R * (R - r) / (R - r)^3 := by field_simp <;> ring
    _ ≤ 16 * M * R^2 / (R - r)^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hM.le (by nlinarith : 0 ≤ R * (R + r))]

end DusartSmoothing.Landau


