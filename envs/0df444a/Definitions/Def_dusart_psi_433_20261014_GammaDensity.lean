-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaDensity
-- name    : dusart_psi_433_20261014_GammaDensity
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:24:11.432646+00:00
-- url     : https://prove2.me/theorems/c26d8616-fc20-467d-a383-1e09cf298844
-- title:
--   Dusart smoothing: Gamma Density
-- statement:
--   This module gives the complete gamma density component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GammaRealStirling
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex Set MeasureTheory

noncomputable section
namespace DusartSmoothing.RvM

def gammaDensity (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + I * t / 2)).re -
    Real.log Real.pi / (2 * Real.pi)

def countingMain (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)

lemma gammaDensity_stirling (t : ℝ) (ht : 1 ≤ |t|) :
    |gammaDensity t - (1 / (2 * Real.pi)) * Real.log (|t| / (2 * Real.pi))| ≤
      10 / (Real.pi * t ^ 2) := by
  have htpos : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hh := DusartSmoothing.StirlingVert.re_digamma_stirlingPrime
    (a := 1 / 4) (by norm_num) (by norm_num) (t := t / 2)
    (by rw [abs_div]; norm_num; linarith)
  have harg : (1 / 4 : ℂ) + I * ((t : ℂ) / 2) = 1 / 4 + I * t / 2 := by ring
  push_cast at hh
  rw [harg, abs_div] at hh
  norm_num at hh
  have hlog : Real.log (|t| / (2 * Real.pi)) =
      Real.log (|t| / 2) - Real.log Real.pi := by
    rw [Real.log_div htpos.ne' (by positivity),
      Real.log_div htpos.ne' (by norm_num),
      Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  have heq : gammaDensity t - (1 / (2 * Real.pi)) * Real.log (|t| / (2 * Real.pi)) =
      (1 / (2 * Real.pi)) *
        ((Complex.digamma (1 / 4 + I * t / 2)).re - Real.log (|t| / 2)) := by
    rw [gammaDensity, hlog]
    ring
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) *
      |(Complex.digamma (1 / 4 + I * t / 2)).re - Real.log (|t| / 2)|
      ≤ (1 / (2 * Real.pi)) * (5 / (t / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp; ring

lemma hasDerivAt_countingMain (t : ℝ) (ht : 0 < t) :
    HasDerivAt countingMain ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) t := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hl := (Real.hasDerivAt_log (div_ne_zero ht.ne' hπ.ne')).comp t
    ((hasDerivAt_id t).div_const (2 * Real.pi))
  have hh := ((hasDerivAt_id t).div_const (2 * Real.pi)).mul (hl.sub_const 1)
  convert hh using 1
  all_goals first | rfl | (dsimp [countingMain]; field_simp [ht.ne', Real.pi_pos.ne']; ring)

lemma continuous_digamma_positive_line (a : ℝ) (ha : 0 < a) :
    Continuous (fun t : ℝ => Complex.digamma (a + I * t)) := by
  have hne : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m hm
    have hh := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hh
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : (0 : ℝ) < (a + I * t : ℂ).re := by simpa using ha
  have hg : AnalyticAt ℂ Complex.Gamma (a + I * t) := hΓ _ hz
  have hdn : AnalyticAt ℂ Complex.digamma (a + I * t) := by
    exact hg.deriv.div hg (Complex.Gamma_ne_zero (hne _ hz))
  have hc : ContinuousAt (fun u : ℝ => (a : ℂ) + I * (u : ℂ)) t := by fun_prop
  exact hdn.continuousAt.comp (f := fun u : ℝ => (a : ℂ) + I * (u : ℂ)) hc

lemma continuous_gammaDensity : Continuous gammaDensity := by
  have hd := (continuous_digamma_positive_line (1 / 4) (by norm_num)).comp
    (show Continuous (fun t : ℝ => t / 2) by fun_prop)
  have haEq : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by push_cast; rfl
  rw [haEq] at hd
  have heq : gammaDensity = (fun t : ℝ =>
      (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + I * (t / 2 : ℝ))).re -
        Real.log Real.pi / (2 * Real.pi)) := by
    funext t
    dsimp [gammaDensity]
    congr 3
    push_cast
    ring
  rw [heq]
  simpa only [Function.comp_def, Pi.sub_apply] using
    ((Complex.continuous_re.comp hd).const_mul (1 / (2 * Real.pi))).fun_sub
      (continuous_const : Continuous (fun _ : ℝ => Real.log Real.pi / (2 * Real.pi)))

lemma counting_density_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ =>
      (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro t ht
  exact div_ne_zero (ne_of_gt (ha.trans_le ht.1)) (by positivity)

lemma integral_counting_density (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) =
      countingMain b - countingMain a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_countingMain t ?_)
    (counting_density_intervalIntegrable a b ha hab)
  rw [uIcc_of_le hab] at ht
  exact ha.trans_le ht.1

lemma reciprocal_square_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1))

lemma integral_reciprocal_square (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -t⁻¹) (f' := fun t : ℝ => 1 / t ^ 2)
    (a := a) (b := b)
    (by intro t ht
        rw [uIcc_of_le hab] at ht
        simpa only [Pi.neg_apply, neg_neg, one_div] using
          (hasDerivAt_inv (ne_of_gt (ha.trans_le ht.1))).fun_neg)
    (reciprocal_square_intervalIntegrable a b ha hab)
  simpa only [one_div, neg_sub_neg] using h

lemma gammaDensity_integral_error_bound (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∫ t in a..b, gammaDensity t) - (countingMain b - countingMain a)| ≤
      10 / (Real.pi * a) := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hap.trans_le hab
  let d : ℝ → ℝ := fun t => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
  have hi : IntervalIntegrable d volume a b := counting_density_intervalIntegrable a b hap hab
  have hγ := continuous_gammaDensity.intervalIntegrable (μ := volume) a b
  have hmaj : IntervalIntegrable (fun t : ℝ => (10 / Real.pi) * (1 / t ^ 2)) volume a b :=
    (reciprocal_square_intervalIntegrable a b hap hab).const_mul _
  have habs := (hγ.sub hi).abs
  rw [← integral_counting_density a b hap hab, ← intervalIntegral.integral_sub hγ hi]
  calc |∫ t in a..b, gammaDensity t - d t|
      ≤ ∫ t in a..b, |gammaDensity t - d t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, (10 / Real.pi) * (1 / t ^ 2) := by
      apply intervalIntegral.integral_mono_on hab habs hmaj
      intro t ht
      have htp : 0 < t := hap.trans_le ht.1
      have hh := gammaDensity_stirling t (by rw [abs_of_pos htp]; linarith [ht.1])
      rw [abs_of_pos htp] at hh
      have he : 10 / (Real.pi * t ^ 2) = (10 / Real.pi) * (1 / t ^ 2) := by
        field_simp [Real.pi_pos.ne', htp.ne'] <;> ring
      rw [he] at hh
      exact hh
    _ = (10 / Real.pi) * (1 / a - 1 / b) := by
      rw [intervalIntegral.integral_const_mul, integral_reciprocal_square a b hap hab]
    _ ≤ 10 / (Real.pi * a) := by
      have hn : 0 ≤ (10 / Real.pi) * (1 / b) := by positivity
      have he : (10 / Real.pi) * (1 / a - 1 / b) =
          10 / (Real.pi * a) - (10 / Real.pi) * (1 / b) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [he]
      linarith

lemma gammaDensity_integral_error_lt_one (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) :
    |(∫ t in a..b, gammaDensity t) - (countingMain b - countingMain a)| < 1 := by
  apply lt_of_le_of_lt (gammaDensity_integral_error_bound a b (by linarith) hab)
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi * a)).2
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hprod : (12 : ℝ) ≤ Real.pi * a := by nlinarith
  linarith

end DusartSmoothing.RvM


