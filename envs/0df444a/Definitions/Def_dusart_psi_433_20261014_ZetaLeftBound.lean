-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaLeftBound
-- name    : dusart_psi_433_20261014_ZetaLeftBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:46:13.358323+00:00
-- url     : https://prove2.me/theorems/91cab972-b615-4319-9581-5c75f20bf98a
-- title:
--   Dusart smoothing: Zeta Left Bound
-- statement:
--   This module gives the complete zeta left bound component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZetaRightBound
import Definitions.Def_dusart_psi_433_20261014_PerronAnalytic
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real Filter Topology

lemma differentiableAt_GammaR_general {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) : DifferentiableAt ℂ Gammaℝ s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Gammaℝ = fun z : ℂ => (Real.pi : ℂ)^(-z / 2) * Gamma (z / 2) := by
    funext z; rw [Gammaℝ_def]
  rw [e]
  exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)).mul
    ((Complex.differentiableAt_Gamma (s / 2) hs).comp s (by fun_prop))

lemma logDeriv_completedZeta_general {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0)
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv completedRiemannZeta s = logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => completedRiemannZeta z / Gammaℝ z := by
    filter_upwards [eventually_ne_nhds h0] with z hz
    exact riemannZeta_def_of_ne_zero hz
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    rw [riemannZeta_def_of_ne_zero h0, h, zero_div] at hζ
    exact hζ rfl
  have h : logDeriv riemannZeta s =
      logDeriv completedRiemannZeta s - logDeriv Gammaℝ s := by
    rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds, ← logDeriv_apply]
    exact logDeriv_div s hΛ hΓ (differentiableAt_completedZeta h0 h1)
      (differentiableAt_GammaR_general hs)
  linear_combination -h

lemma abs_log_pi_le_three : |Real.log Real.pi| ≤ 3 := by
  have h1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  have h := Real.log_le_sub_one_of_pos Real.pi_pos
  linarith [Real.pi_lt_four]

lemma norm_logDeriv_GammaR_left (t : ℝ) :
    ‖logDeriv Gammaℝ (-(1 / 2 : ℂ) + t * I)‖ ≤ |t| / 2 + 6 := by
  have he : (-(1 / 2 : ℂ) + t * I) / 2 = -(1 / 4 : ℂ) + t * I / 2 := by ring
  have hs : ∀ m : ℕ, (-(1 / 2 : ℂ) + t * I) / 2 ≠ -(m : ℂ) := by
    rw [he]; exact neg_quarter_not_neg_nat t
  rw [logDeriv_GammaR_general hs, he]
  have hn := norm_add_le (-(Real.log Real.pi : ℂ) / 2)
    ((1 / 2 : ℂ) * Complex.digamma (-(1 / 4 : ℂ) + t * I / 2))
  norm_num [norm_mul, norm_div] at hn
  have hψ := norm_digamma_neg_quarter t
  linarith [abs_log_pi_le_three]

lemma norm_logDeriv_GammaR_right (t : ℝ) :
    ‖logDeriv Gammaℝ ((3 / 2 : ℂ) + t * I)‖ ≤ |t| / 2 + 4 := by
  have he : ((3 / 2 : ℂ) + t * I) / 2 = (3 / 4 : ℂ) + t * I / 2 := by ring
  have hs : ∀ m : ℕ, ((3 / 2 : ℂ) + t * I) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hh := congrArg Complex.re hm
    norm_num at hh
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [logDeriv_GammaR_general hs, he]
  have hn := norm_add_le (-(Real.log Real.pi : ℂ) / 2)
    ((1 / 2 : ℂ) * Complex.digamma ((3 / 4 : ℂ) + t * I / 2))
  norm_num [norm_mul, norm_div] at hn
  have hψ := norm_digamma_three_quarters t
  linarith [abs_log_pi_le_three]

lemma logDeriv_zeta_left_reflection (t : ℝ) :
    logDeriv riemannZeta (-(1 / 2 : ℂ) + t * I) =
      -logDeriv riemannZeta ((3 / 2 : ℂ) - t * I) -
      logDeriv Gammaℝ (-(1 / 2 : ℂ) + t * I) -
      logDeriv Gammaℝ ((3 / 2 : ℂ) - t * I) := by
  let s : ℂ := -(1 / 2) + t * I
  have h0 : s ≠ 0 := by intro h; have hh := congrArg Complex.re h; norm_num [s] at hh
  have h1 : s ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num [s] at hh
  have hζ : riemannZeta s ≠ 0 := zeta_nonzero_left_half_strip s (by norm_num [s]) (by norm_num [s])
  have hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    have he : s / 2 = -(1 / 4 : ℂ) + t * I / 2 := by dsimp [s]; ring
    rw [he]; exact neg_quarter_not_neg_nat t
  have hΓ : Gammaℝ s ≠ 0 := by
    rw [Gammaℝ_def]
    exact mul_ne_zero (by simp [Real.pi_ne_zero]) (Gamma_ne_zero hs)
  have he : 1 - s = (3 / 2 : ℂ) - t * I := by dsimp [s]; ring
  have hζr : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num [s])
  have h1r : 1 - s ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num [s] at hh
  have hr := logDeriv_completedZeta (1 - s) h1r hζr (by norm_num [s])
  have hl := logDeriv_completedZeta_general h0 h1 hζ hΓ hs
  have hf := logDeriv_completedZeta_one_sub s h0 h1
  rw [he] at hr hf
  change logDeriv riemannZeta s = _
  linear_combination -hr - hl + hf

lemma norm_logDeriv_zeta_left (t : ℝ) :
    ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + t * I)‖ ≤ |t| + 32 := by
  rw [logDeriv_zeta_left_reflection]
  have he : (3 / 2 : ℂ) - t * I = (3 / 2 : ℂ) + (-t) * I := by ring
  have hZ := DusartSmoothing.norm_logDeriv_zeta_three_halves (-t)
  have hG := norm_logDeriv_GammaR_right (-t)
  rw [Complex.ofReal_neg, ← he] at hZ hG
  rw [abs_neg] at hG
  have hn := (norm_sub_le
    (-logDeriv riemannZeta ((3 / 2 : ℂ) - t * I) - logDeriv Gammaℝ (-(1 / 2 : ℂ) + t * I))
    (logDeriv Gammaℝ ((3 / 2 : ℂ) - t * I))).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_neg] at hn
  linarith [norm_logDeriv_GammaR_left t]

end DusartSmoothing.RvM


