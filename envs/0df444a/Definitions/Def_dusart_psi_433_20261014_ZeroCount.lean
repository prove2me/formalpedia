-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroCount
-- name    : dusart_psi_433_20261014_ZeroCount
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:26:28.343841+00:00
-- url     : https://prove2.me/theorems/1da9f302-dd5c-4c87-bd6c-c6ec5a724626
-- title:
--   Dusart smoothing: Zero Count
-- statement:
--   This module gives the complete zero count component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_CountContour
import Definitions.Def_dusart_psi_433_20261014_ContourFold
import Definitions.Def_dusart_psi_433_20261014_ContourSplit
import Definitions.Def_dusart_psi_433_20261014_GammaContour
import Definitions.Def_dusart_psi_433_20261014_VerticalArgument
import Definitions.Def_dusart_psi_433_20261014_ZetaGrowth
import Definitions.Def_dusart_psi_433_20261014_LowHeight
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set MeasureTheory Real
open DusartSmoothing.Contour

lemma Ncount_eq_gamma_and_zeta {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hga : GoodHeight a) (hgb : GoodHeight b) :
    (Ncount a b : ℝ) = (∫ t in a..b, gammaDensity t) +
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) a b).im := by
  have hc := rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount
    (by linarith : 0 < a) hab.le hga hgb
  have hf := rectangleIntegral_logDeriv_completedZeta_eq_halfContour ha hab hga hgb
  change (1 / (2 * (Real.pi : ℂ) * I)) *
    RectangleIntegral (logDeriv completedRiemannZeta) (-1 + a * I) (2 + b * I) = _ at hc
  rw [hf] at hc
  have he : ∀ u : ℝ, (1 / (2 * (Real.pi : ℂ) * I)) * (2 * I * (u : ℂ)) =
      ((1 / Real.pi * u : ℝ) : ℂ) := by
    intro u
    push_cast
    field_simp [Real.pi_ne_zero, I_ne_zero]
  rw [he] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.natCast_re] at hr
  rw [halfContour_completedZeta_split ha hab hga hgb, Complex.add_im] at hr
  have hΓ := gamma_side (T₁ := a) (T₂ := b) (by linarith) (by linarith)
  linarith

lemma goodHeight_four : GoodHeight 4 := by
  intro ρ hρ he
  exact DusartSmoothing.LowHeight.zeta_nonzero_small_height ρ hρ.2.1 hρ.2.2.le
    (by rw [he]; norm_num) (by rw [he]) hρ.1

lemma zeta_nonzero_horizontal_of_good {T : ℝ} (hT : 4 ≤ T) (hg : GoodHeight T) :
    ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0 := by
  intro σ hσ
  exact (path_point_facts (s := σ + T * I) (by simp; linarith [hσ.1])
    (by simpa using (show 1 ≤ T by linarith)) (by simpa using hg)).2

lemma zeta_halfContour_bound {a b : ℝ} (ha : 4 ≤ a) (hb : 4 ≤ b)
    (hga : GoodHeight a) (hgb : GoodHeight b) :
    |(halfContour (logDeriv riemannZeta) a b).im| ≤
      Real.pi * (9 * Real.log (a + 5) + 9 * Real.log (b + 5) + 57) := by
  have ha' := actual_backlund_horizontal_numerical_bound a ha
    (zeta_nonzero_horizontal_of_good ha hga)
  have hb' := actual_backlund_horizontal_numerical_bound b hb
    (zeta_nonzero_horizontal_of_good hb hgb)
  have hv := vertical_two a b
  rw [intervalIntegral.integral_mul_const] at hv
  simp only [halfContour, Complex.add_im, Complex.sub_im]
  calc |(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + a * I)).im +
      ((∫ t in a..b, logDeriv riemannZeta (2 + t * I)) * I).im -
      (∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + b * I)).im|
      ≤ |(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + a * I)).im| +
        |((∫ t in a..b, logDeriv riemannZeta (2 + t * I)) * I).im| +
        |(∫ σ in (1/2 : ℝ)..2, logDeriv riemannZeta (σ + b * I)).im| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

lemma abs_countingMain_four_le_one : |countingMain 4| ≤ 1 := by
  have hπ : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hpos : 0 < 2 / Real.pi := by positivity
  have hsmall : 2 / Real.pi < 1 := (div_lt_one Real.pi_pos).2 hπ
  have hlog : Real.log (2 / Real.pi) < 0 := Real.log_neg hpos hsmall
  have hinv : Real.log (2 / Real.pi) = -Real.log (Real.pi / 2) := by
    rw [Real.log_div (by norm_num) Real.pi_pos.ne',
      Real.log_div Real.pi_pos.ne' (by norm_num)]
    ring
  have hbound := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.pi / 2)
  have hmain : countingMain 4 = (2 / Real.pi) * (Real.log (2 / Real.pi) - 1) := by
    have hd : (4 : ℝ) / (2 * Real.pi) = 2 / Real.pi := by field_simp; ring
    simp only [countingMain, hd]
  rw [hmain, abs_mul, abs_of_pos hpos, abs_of_neg (by linarith)]
  rw [hinv]
  calc (2 / Real.pi) * -( -Real.log (Real.pi / 2) - 1)
      ≤ (2 / Real.pi) * (Real.pi / 2) := by gcongr; linarith
    _ = 1 := by field_simp

lemma nine_log_nine_lt_twenty : (9 : ℝ) * Real.log 9 < 20 := by
  have hexp : (9 : ℝ) < Real.exp (20 / 9 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 20 / 9) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9)).2 hexp
  linarith

lemma Ncount_four_error_good {T : ℝ} (hT : 4 < T) (hg : GoodHeight T) :
    |(Ncount 4 T : ℝ) - countingMain T| < 9 * Real.log (T + 5) + 79 := by
  have he := Ncount_eq_gamma_and_zeta (a := 4) (by norm_num) hT goodHeight_four hg
  have hΓ := gammaDensity_integral_error_lt_one 4 T (by norm_num) hT.le
  have hz := zeta_halfContour_bound (a := 4) (b := T) (by norm_num) hT.le goodHeight_four hg
  have hp : 0 < 1 / Real.pi := by positivity
  have hz' : |(1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im| ≤
      9 * Real.log 9 + 9 * Real.log (T + 5) + 57 := by
    rw [abs_mul, abs_of_pos hp]
    calc (1 / Real.pi) * |(halfContour (logDeriv riemannZeta) 4 T).im|
        ≤ (1 / Real.pi) * (Real.pi *
          (9 * Real.log (4 + 5) + 9 * Real.log (T + 5) + 57)) :=
          mul_le_mul_of_nonneg_left hz hp.le
      _ = _ := by norm_num <;> field_simp
  rw [he]
  have heq : (∫ t in (4 : ℝ)..T, gammaDensity t) +
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im - countingMain T =
      ((∫ t in (4 : ℝ)..T, gammaDensity t) - (countingMain T - countingMain 4)) -
      countingMain 4 + (1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im := by ring
  rw [heq]
  calc |((∫ t in (4 : ℝ)..T, gammaDensity t) - (countingMain T - countingMain 4)) -
        countingMain 4 + (1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im|
      ≤ |(∫ t in (4 : ℝ)..T, gammaDensity t) - (countingMain T - countingMain 4)| +
        |countingMain 4| + |(1 / Real.pi) * (halfContour (logDeriv riemannZeta) 4 T).im| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ < _ := by linarith [abs_countingMain_four_le_one, nine_log_nine_lt_twenty]

end DusartSmoothing.RvM


