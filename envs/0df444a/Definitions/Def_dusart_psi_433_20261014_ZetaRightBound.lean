-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaRightBound
-- name    : dusart_psi_433_20261014_ZetaRightBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:43:10.152765+00:00
-- url     : https://prove2.me/theorems/a9f39283-7d4f-48ed-912f-93181fd3c4a1
-- title:
--   Dusart smoothing: Zeta Right Bound
-- statement:
--   This module gives the complete zeta right bound component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PerronRightLine
import Definitions.Def_dusart_psi_433_20261014_GammaRGeneral
noncomputable section
namespace DusartSmoothing
open Complex Real MeasureTheory Filter Topology

lemma log_le_four_rpow_quarter (y : ℝ) (hy : 0 < y) :
    Real.log y ≤ 4 * y ^ (1 / 4 : ℝ) := by
  have hp := Real.rpow_pos_of_pos hy (1 / 4 : ℝ)
  have h := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hy] at h
  linarith

lemma real_zeta_five_quarters_sum :
    (∑' n : ℕ, 1 / (n : ℝ) ^ (5 / 4 : ℝ)) ≤ 11 / 2 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (5 / 4 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have he : (∑' n : ℕ, 1 / (n : ℝ) ^ (5 / 4 : ℝ)) =
      (riemannZeta (5 / 4 : ℂ)).re := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num)]
    rw [Complex.re_tsum ((Complex.summable_one_div_nat_cpow (p := (5 / 4 : ℂ))).mpr (by norm_num))]
    apply tsum_congr
    intro n
    have h : ((1 / (n : ℝ) ^ (5 / 4 : ℝ) : ℝ) : ℂ) =
        1 / (n : ℂ) ^ (5 / 4 : ℂ) := by
      simpa using (by rw [Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]; norm_num :
        ((1 / (n : ℝ) ^ (5 / 4 : ℝ) : ℝ) : ℂ) = 1 / (n : ℂ) ^ (5 / 4 : ℂ))
    exact congrArg Complex.re h
  rw [he]
  have h := RvM.norm_riemannZeta_le_of_re_pos (s := (5 / 4 : ℂ)) (by norm_num) (by norm_num)
  norm_num [Complex.norm_real, Real.norm_eq_abs] at h
  exact (Complex.re_le_norm _).trans h

lemma vonMangoldt_three_halves_term_bound (t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℂ) + t * I) n‖ ≤ 4 * (1 / (n : ℝ) ^ (5 / 4 : ℝ)) := by
  by_cases hn : n = 0
  · subst n; simp [LSeries.term]
  have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hRe : ((3 / 2 : ℂ) + t * I).re = (3 / 2 : ℝ) := by norm_num
  rw [LSeries.norm_term_eq, if_neg hn, hRe]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
  calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)
      ≤ (4 * (n : ℝ) ^ (1 / 4 : ℝ)) / (n : ℝ) ^ (3 / 2 : ℝ) := by
        apply div_le_div_of_nonneg_right
          ((ArithmeticFunction.vonMangoldt_le_log).trans (log_le_four_rpow_quarter n hp))
          (Real.rpow_nonneg hp.le _)
    _ = 4 * (1 / (n : ℝ) ^ (5 / 4 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hp.le, mul_assoc, ← Real.rpow_add hp]
      norm_num [Real.rpow_neg hp.le]

lemma norm_logDeriv_zeta_three_halves (t : ℝ) :
    ‖logDeriv riemannZeta ((3 / 2 : ℂ) + t * I)‖ ≤ 22 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs : LSeriesSummable f ((3 / 2 : ℂ) + t * I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have he : LSeries f ((3 / 2 : ℂ) + t * I) =
      -logDeriv riemannZeta ((3 / 2 : ℂ) + t * I) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by norm_num)]
    simp only [logDeriv_apply, neg_div]
  have h := norm_tsum_le_tsum_norm hs.norm
  rw [show (∑' n, LSeries.term f ((3 / 2 : ℂ) + t * I) n) =
    LSeries f ((3 / 2 : ℂ) + t * I) from rfl, he, norm_neg] at h
  refine h.trans ?_
  calc (∑' n, ‖LSeries.term f ((3 / 2 : ℂ) + t * I) n‖)
      ≤ ∑' n : ℕ, 4 * (1 / (n : ℝ) ^ (5 / 4 : ℝ)) := by
        exact hs.norm.tsum_le_tsum (vonMangoldt_three_halves_term_bound t)
          ((Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4)
    _ = 4 * ∑' n : ℕ, 1 / (n : ℝ) ^ (5 / 4 : ℝ) := tsum_mul_left
    _ ≤ 22 := by linarith [real_zeta_five_quarters_sum]

end DusartSmoothing


