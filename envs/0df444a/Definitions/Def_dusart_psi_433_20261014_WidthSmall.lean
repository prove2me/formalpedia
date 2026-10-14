-- Prove2me | Definitions.Def_dusart_psi_433_20261014_WidthSmall
-- name    : dusart_psi_433_20261014_WidthSmall
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:22:29.657586+00:00
-- url     : https://prove2.me/theorems/abce4273-b8f9-402f-8ca2-944a8e27266e
-- title:
--   Dusart smoothing: Width Small
-- statement:
--   This module gives the complete width small component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WidthElementary
noncomputable section
namespace DusartSmoothing
open Real Set

lemma sqrt_exp_neg_lt_one_thousandth (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    Real.sqrt X * Real.exp (-X) < (1 / 1000 : ℝ) := by
  let f : ℝ → ℝ := fun y => y * Real.exp (-y)
  have hd : ∀ y, HasDerivAt f ((1 - y) * Real.exp (-y)) y := by
    intro y
    convert (hasDerivAt_id y).mul ((hasDerivAt_id y).neg.exp) using 1 <;> try rfl
    dsimp
    ring
  have hmono : AntitoneOn f (Ici (836 / 100 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by dsimp [f]; fun_prop)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y).deriv]
    have hy' : (836 / 100 : ℝ) < y := by simpa only [interior_Ici, mem_Ioi] using hy
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)
  have hf := hmono (by simp) (Set.mem_Ici.mpr hX.le) hX.le
  have he : Real.exp (-(836 / 100 : ℝ)) < (1 / 4262 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4262) exp_threshold_lower
  have hbase := mul_lt_mul_of_pos_left he (by norm_num : (0 : ℝ) < 836 / 100)
  have hs : Real.sqrt X ≤ X / 2 := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ X)
    nlinarith [Real.sqrt_nonneg X]
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (-X))
  dsimp [f] at hf
  nlinarith

lemma optimalWidth_lt_one_thousandth (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    optimalWidth X ν < (1 / 1000 : ℝ) := by
  have h := optimalWidth_le_four_fifths X ν hX hν hν1 hk
  have hb := sqrt_exp_neg_lt_one_thousandth X hX
  nlinarith

lemma balanced_width_exp_lower (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    2 * Real.exp (-X) ≤ optimalWidth X ν := by
  have hp := optimalWidth_pos X ν hX hν
  have hh := balanced_width_height_ge_two X ν hX hν hν1 hk
  have hT : transformHeight X ν ≤ Real.exp X := by
    unfold transformHeight
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ X by linarith) (sub_nonneg.mpr hν1)]
  have hm := mul_le_mul_of_nonneg_left hT hp.le
  rw [Real.exp_neg]
  apply (mul_inv_le_iff₀ (Real.exp_pos X)).2
  linarith

lemma smoothing_lower_base_ge_one (R x ν : ℝ) (hR : 0 < R) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k (X R x) ν = 1) :
    1 ≤ x - 2 * (optimalWidth (X R x) ν * x) := by
  have hf := threshold_facts R x hR hX
  have hδ := optimalWidth_lt_one_thousandth (X R x) ν hf.1 hν hν1 hk
  have hlog := Real.log_le_sub_one_of_pos hx
  have hxp : 4 ≤ x := by linarith [hf.2.2.2]
  have hm := mul_le_mul_of_nonneg_right (show optimalWidth (X R x) ν ≤ (1 / 4 : ℝ) by linarith) hx.le
  nlinarith

end DusartSmoothing


