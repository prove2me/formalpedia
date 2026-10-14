-- Prove2me | Definitions.Def_dusart_psi_433_20261014_WidthElementary
-- name    : dusart_psi_433_20261014_WidthElementary
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:25.828186+00:00
-- url     : https://prove2.me/theorems/580200f3-2758-414f-acbc-b79fe8a840e9
-- title:
--   Dusart smoothing: Width Elementary
-- statement:
--   This module gives the complete width elementary component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_FactorBounds
import Definitions.Def_dusart_psi_433_20261014_CountingMarginTail
noncomputable section
namespace DusartSmoothing
open Real Set

lemma balanced_width_height_ge_two (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    2 ≤ optimalWidth X ν * transformHeight X ν := by
  have h0 := G0_pos X ν hX hν
  have hG := G0_lt_G1 X ν hX hν hν1
  have hb := optimalWidth_balances X ν hX hν hν1 hk
  have hp := mul_pos (optimalWidth_pos X ν hX hν) (transformHeight_pos X ν)
  have hh : 4 ≤ (optimalWidth X ν * transformHeight X ν)^2 := by nlinarith
  nlinarith

lemma optimalWidth_le_four_fifths (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    optimalWidth X ν ≤ (4 / 5 : ℝ) * Real.sqrt X * Real.exp (-X) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hs : Real.sqrt (2 / Real.pi) ≤ (4 / 5 : ℝ) := by
    have hπ : (25 / 8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    have hq : 2 / Real.pi ≤ (16 / 25 : ℝ) :=
      (div_le_iff₀ Real.pi_pos).2 (by linarith)
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi), Real.sqrt_nonneg (2 / Real.pi)]
  have hu := U_lt_one X ν hX hν hν1
  have hroot : Real.sqrt (Real.sqrt (U X ν)) ≤ 1 := by
    exact Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hu.le)
  have he : Real.exp (-Y X ν / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Y_nonneg X ν hXp.le hνp])
  rw [optimalWidth_formula X ν hX hν hν1 hk]
  have hm : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
      Real.exp (-Y X ν / 2) ≤ (4 / 5 : ℝ) := by
    exact ((mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) he).trans
      ((mul_le_of_le_one_right (Real.sqrt_nonneg _) hroot).trans hs))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg X)) (Real.exp_nonneg _)

lemma exp_threshold_lower : (4262 : ℝ) < Real.exp (836 / 100 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 836 / 100) 30
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma exp_neg_threshold_bound (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    Real.exp (-X) < (1 / 4262 : ℝ) := by
  rw [Real.exp_neg]
  simpa only [one_div] using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4262) (exp_threshold_lower.trans (Real.exp_lt_exp.mpr hX)))

lemma reflection_numerical_margin (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) :
    (16 * Real.exp (-2 * X) + 6 * Real.exp (-X)) * (X + 2) / ν < (2 / 100 : ℝ) := by
  let f : ℝ → ℝ := fun y => (y + 2) * Real.exp (-y)
  have hd : ∀ y, HasDerivAt f ((-y - 1) * Real.exp (-y)) y := by
    intro y
    convert (((hasDerivAt_id y).add_const 2).mul ((hasDerivAt_id y).neg.exp)) using 1 <;> try rfl
    dsimp; ring
  have hmono : AntitoneOn f (Ici (836 / 100 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by dsimp [f]; fun_prop)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y).deriv]
    have hy' : (836 / 100 : ℝ) < y := by simpa only [interior_Ici, mem_Ioi] using hy
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)
  have hf := hmono (by simp) (Set.mem_Ici.mpr hX.le) hX.le
  have hb : f (836 / 100 : ℝ) < ((836 / 100 : ℝ) + 2) / 4262 := by
    dsimp [f]
    have hi : Real.exp (-(836 / 100 : ℝ)) < (1 / 4262 : ℝ) := by
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4262) exp_threshold_lower
    have hm := mul_lt_mul_of_pos_left hi (by norm_num : (0 : ℝ) < 836 / 100 + 2)
    rwa [mul_one_div] at hm
  have he := exp_neg_threshold_bound X hX
  have he2 : Real.exp (-2 * X) = Real.exp (-X)^2 := by
    rw [← Real.exp_nat_mul]; congr 1 <;> norm_num <;> ring
  have hmain : (16 * Real.exp (-2 * X) + 6 * Real.exp (-X)) * (X + 2) ≤
      7 * f X := by
    rw [he2]
    have hp : 0 ≤ Real.exp (-X) := Real.exp_nonneg _
    have hm : 16 * Real.exp (-X)^2 + 6 * Real.exp (-X) ≤ 7 * Real.exp (-X) := by nlinarith
    have h := mul_le_mul_of_nonneg_right hm (show 0 ≤ X + 2 by linarith)
    dsimp [f]
    nlinarith only [h]
  apply (div_lt_iff₀ (by linarith : 0 < ν)).2
  have hfn := hf.trans_lt hb
  dsimp [f] at hfn
  nlinarith

end DusartSmoothing


