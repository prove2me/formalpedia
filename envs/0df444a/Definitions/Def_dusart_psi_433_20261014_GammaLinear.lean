-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaLinear
-- name    : dusart_psi_433_20261014_GammaLinear
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:22:02.028592+00:00
-- url     : https://prove2.me/theorems/bdacef14-bfbe-4b6c-b91f-f0f88e50a20b
-- title:
--   Dusart smoothing: Gamma Linear
-- statement:
--   This module gives the complete gamma linear component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GammaDigammaSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

noncomputable section
namespace DusartSmoothing.RvM
open Complex Real Set

lemma norm_digamma_linear {w : ℂ} (hw : 0 < w.re) (hz : w ∈ Complex.integerComplement) :
    ‖Complex.digamma w‖ ≤ 2 * ‖w‖ + ‖1 / w‖ + 1 := by
  let f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) - 1 / (w + n + 1)
  have hs := DusartSmoothing.DigammaSeries.hasSum_digamma_series hz
  have hseries : HasSum f (Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w) := hs
  have hreal : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) (Real.pi^2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun (fun n => by simp)
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ ‖w‖ * (1 / ((n : ℝ) + 1)^2) := by
    intro n
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have ha : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hp.ne'
    have hb : w + n + 1 ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hh
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have he : f n = w / (((n : ℂ) + 1) * (w + n + 1)) := by
      dsimp [f]
      field_simp [ha, hb]
      ring
    have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
    have hnorm : (n : ℝ) + 1 ≤ ‖w + n + 1‖ := by
      have h := Complex.re_le_norm (w + n + 1)
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at h
      linarith
    rw [he, norm_div, norm_mul, hn]
    calc ‖w‖ / (((n : ℝ) + 1) * ‖w + n + 1‖) ≤ ‖w‖ / ((n : ℝ) + 1)^2 := by
          apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          nlinarith
      _ = _ := by ring
  have hsum : ‖Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w‖ ≤
      ‖w‖ * (Real.pi^2 / 6) := by
    rw [← hseries.tsum_eq]
    calc ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hseries.summable.norm
      _ ≤ ∑' n : ℕ, ‖w‖ * (1 / ((n : ℝ) + 1)^2) :=
        hseries.summable.norm.tsum_le_tsum hterm (hreal.mul_left ‖w‖).summable
      _ = _ := (hreal.mul_left ‖w‖).tsum_eq
  have hπ : Real.pi^2 / 6 ≤ 2 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hγ : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have he : Complex.digamma w =
      (Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w) -
        (Real.eulerMascheroniConstant : ℂ) - 1 / w := by ring
  have hnorm : ‖Complex.digamma w‖ ≤
      ‖Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w‖ +
      ‖(Real.eulerMascheroniConstant : ℂ)‖ + ‖1 / w‖ := by
    conv_lhs => rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  nlinarith [norm_nonneg w]

end DusartSmoothing.RvM


