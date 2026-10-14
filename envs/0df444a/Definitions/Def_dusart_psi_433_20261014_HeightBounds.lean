-- Prove2me | Definitions.Def_dusart_psi_433_20261014_HeightBounds
-- name    : dusart_psi_433_20261014_HeightBounds
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:43:35.982477+00:00
-- url     : https://prove2.me/theorems/b5887d96-12fa-45c2-bbf7-e4cf8f9b4cb7
-- title:
--   Dusart smoothing: Height Bounds
-- statement:
--   This module gives the complete height bounds component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_FactorBounds
import Definitions.Def_dusart_psi_433_20261014_DecreasingWeight
noncomputable section
namespace DusartSmoothing
open Real

lemma G0_gt_seven_tenths (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) : (7 / 10 : ℝ) < G0 X ν := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  let c : ℝ := 97 / 100 - (18379 / 10000) / (836 / 100)
  have hc : 0 ≤ c := by norm_num [c]
  have hq : Real.log (2 * Real.pi) / X ≤ (18379 / 10000 : ℝ) / (836 / 100) :=
    div_le_div₀ (by norm_num) log_two_pi_upper_precise.le (by norm_num) hX.le
  have hs : (97 / 100 : ℝ)^2 ≤ ν^2 := by nlinarith
  have hd : c ≤ ν - Real.log (2 * Real.pi) / X := by dsimp [c]; linarith
  have hm := mul_le_mul hs hd hc (sq_nonneg ν)
  have hbase : (7 / 10 : ℝ) < (97 / 100 : ℝ)^2 * c := by norm_num [c]
  exact hbase.trans_le hm

lemma sqrt_X_gt_289 (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    (289 / 100 : ℝ) < Real.sqrt X := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ X)
  nlinarith [Real.sqrt_nonneg X]

lemma transformHeight_gt_five_hundred (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) : (500 : ℝ) < transformHeight X ν := by
  have hu : (7 : ℝ) < X * ν := by
    have hXp : 0 < X := by linarith
    have hνp : 0 < ν := by linarith
    nlinarith [mul_pos (by linarith : 0 < X - 836 / 100) (by linarith : 0 < ν - 97 / 100)]
  have he : (500 : ℝ) < Real.exp 7 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  exact he.trans (Real.exp_lt_exp.mpr hu)

lemma transformHeight_seed_lower (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hseed : seed X ≤ ν) : (5 / 2 : ℝ) * Real.exp X ≤ Real.sqrt X * transformHeight X ν := by
  have hXp : 0 < X := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  have h : 1 ≤ X / (2 * Real.pi) * Real.exp (-2 * X * (1 - ν)) := by
    calc
      1 = X / (2 * Real.pi) * Real.exp (-2 * X * (1 - seed X)) :=
        (seed_exponential_cancellation X hXp).symm
      _ ≤ X / (2 * Real.pi) * Real.exp (-2 * X * (1 - ν)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hXp.le (sub_nonneg.mpr hseed)]
  have he : Real.exp (-2 * X * (1 - ν)) = transformHeight X ν ^ 2 / (Real.exp X)^2 := by
    rw [transformHeight, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    norm_num
    ring
  rw [he] at h
  have hn : 1 ≤ (X * transformHeight X ν ^ 2) / (2 * Real.pi * (Real.exp X)^2) := by
    convert h using 1 <;> ring
  have hm := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * (Real.exp X)^2)).1 hn
  have hs : ((5 / 2 : ℝ) * Real.exp X)^2 ≤ (Real.sqrt X * transformHeight X ν)^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hXp.le]
    have hp : (25 / 4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_d2]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (Real.exp X))
    nlinarith
  have hp : 0 ≤ Real.sqrt X * transformHeight X ν :=
    mul_nonneg (Real.sqrt_nonneg X) (transformHeight_pos X ν).le
  have hq : 0 ≤ (5 / 2 : ℝ) * Real.exp X := by positivity
  nlinarith [sq_nonneg (Real.sqrt X * transformHeight X ν - (5 / 2 : ℝ) * Real.exp X)]

lemma zeroCountErrorBound_height (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) :
    zeroCountErrorBound (transformHeight X ν) ≤ 9 * X + 791 / 10 := by
  have hXp : 0 < X := by linarith
  have hT := transformHeight_pos X ν
  have h500 := transformHeight_gt_five_hundred X ν hX hν
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 5 / transformHeight X ν)
  have he : transformHeight X ν + 5 = transformHeight X ν * (1 + 5 / transformHeight X ν) := by
    field_simp
  have hlog : Real.log (transformHeight X ν + 5) ≤ X + 5 / transformHeight X ν := by
    rw [he, Real.log_mul hT.ne' (by positivity), transformHeight, Real.log_exp]
    have hm := mul_nonneg hXp.le (sub_nonneg.mpr hν1)
    change Real.log (1 + 5 / Real.exp (X * ν)) ≤ 1 + 5 / Real.exp (X * ν) - 1 at hl
    linarith
  have h45 : 45 / transformHeight X ν ≤ (1 / 10 : ℝ) :=
    (div_le_iff₀ hT).2 (by linarith)
  unfold zeroCountErrorBound
  nlinarith

lemma gaussian_tail_denominator_ge (ν : ℝ) (hν : (97 / 100 : ℝ) < ν) :
    (19 / 10 : ℝ) ≤ 3 - 1 / ν^2 := by
  have hνp : 0 < ν := by linarith
  have h := (div_le_iff₀ (sq_pos_of_pos hνp)).2 (show (1 : ℝ) ≤ (11 / 10) * ν^2 by nlinarith)
  linarith

end DusartSmoothing


