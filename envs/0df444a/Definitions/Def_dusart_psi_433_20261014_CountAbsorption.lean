-- Prove2me | Definitions.Def_dusart_psi_433_20261014_CountAbsorption
-- name    : dusart_psi_433_20261014_CountAbsorption
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:44:48.346926+00:00
-- url     : https://prove2.me/theorems/8621c145-4dce-4dcc-a067-8327c3a529f2
-- title:
--   Dusart smoothing: Count Absorption
-- statement:
--   This module gives the complete count absorption component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_CountTailEnvelope
import Definitions.Def_dusart_psi_433_20261014_HeightBounds
import Definitions.Def_dusart_psi_433_20261014_CountingMarginTail
import Definitions.Def_dusart_psi_433_20261014_GaussianWeights
noncomputable section
namespace DusartSmoothing
open Real

lemma tail_weight_balance (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    4 / optimalWidth X ν ^ 2 * gaussianTailZeroWeight X (transformHeight X ν) ≤
      gaussianZeroWeight X (transformHeight X ν) := by
  have hδ := optimalWidth_pos X ν hX hν
  have hT := transformHeight_pos X ν
  have h0 := G0_pos X ν hX hν
  have h1 := G1_pos X ν hX hν hν1
  have hb := optimalWidth_balances X ν hX hν hν1 hk
  have hG := G0_lt_G1 X ν hX hν hν1
  have hh : 4 ≤ optimalWidth X ν ^ 2 * transformHeight X ν ^ 2 := by
    nlinarith
  have hr : 4 / (optimalWidth X ν^2 * transformHeight X ν^2) ≤ 1 :=
    (div_le_one (mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hT))).2 hh
  unfold gaussianTailZeroWeight gaussianZeroWeight
  have hm := mul_le_mul_of_nonneg_right hr
    (div_nonneg (Real.exp_nonneg (-X^2 / Real.log (transformHeight X ν))) hT.le)
  rw [show 4 / optimalWidth X ν^2 * (Real.exp (-X^2 / Real.log (transformHeight X ν)) / transformHeight X ν^3) =
    (4 / (optimalWidth X ν^2 * transformHeight X ν^2)) *
      (Real.exp (-X^2 / Real.log (transformHeight X ν)) / transformHeight X ν) by
      field_simp <;> ring]
  simpa only [one_mul] using hm

lemma count_tail_envelope_at_height (X ν : ℝ) (hX : X ≠ 0) (hν : ν ≠ 0) :
    gaussianCountTailEnvelope X (X * ν) =
      gaussianTailZeroWeight X (transformHeight X ν) / (3 - 1 / ν^2) := by
  unfold gaussianCountTailEnvelope gaussianTailZeroWeight transformHeight
  rw [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_sub]
  have he : X^2 / (X * ν)^2 = 1 / ν^2 := by field_simp [hX, hν] <;> ring
  rw [he]
  congr 1
  ring

lemma low_weight_width_identity (X ν : ℝ) (hX : X ≠ 0) (hν : ν ≠ 0) :
    optimalWidth X ν = X / Real.pi * G0 X ν * transformHeight X ν *
      gaussianZeroWeight X (transformHeight X ν) := by
  unfold gaussianZeroWeight
  rw [transformHeight, Real.log_exp]
  have he : -X^2 / (X * ν) = -X / ν := by field_simp [hX, hν] <;> ring
  rw [he, lower_exponential_identity X ν hν]
  dsimp [optimalWidth, balanceCoefficient, transformHeight]
  field_simp
  <;> ring

lemma counting_loss_absorbed (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed X ≤ ν)
    (hk : k X ν = 1) :
    2 * zeroCountErrorBound (transformHeight X ν) * gaussianZeroWeight X (transformHeight X ν) +
      8 / optimalWidth X ν^2 * zeroCountErrorBound (transformHeight X ν) * gaussianTailZeroWeight X (transformHeight X ν) +
      36 / optimalWidth X ν^2 * gaussianCountTailEnvelope X (X * ν) <
        (98 / 100 : ℝ) * (optimalWidth X ν * ν / (X + 2 * ν)) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hδ := optimalWidth_pos X ν hX hν
  have hT := transformHeight_pos X ν
  have hg : 0 ≤ gaussianZeroWeight X (transformHeight X ν) := by
    unfold gaussianZeroWeight; positivity
  have hE : 0 ≤ zeroCountErrorBound (transformHeight X ν) := by
    unfold zeroCountErrorBound
    have hl : 0 ≤ Real.log (transformHeight X ν + 5) := Real.log_nonneg (by linarith)
    linarith
  have hb := tail_weight_balance X ν hX hν hν1 hk
  have hd := gaussian_tail_denominator_ge ν hν
  have he := count_tail_envelope_at_height X ν hXp.ne' hνp.ne'
  have ht : 9 / (3 - 1 / ν^2) ≤ (6 / 5 : ℝ) * 4 :=
    (div_le_iff₀ (by linarith : 0 < 3 - 1 / ν^2)).2 (by linarith)
  have htail : 36 / optimalWidth X ν^2 * gaussianCountTailEnvelope X (X * ν) ≤
      (24 / 5 : ℝ) * gaussianZeroWeight X (transformHeight X ν) := by
    rw [he]
    have hgt : 0 ≤ 4 / optimalWidth X ν^2 * gaussianTailZeroWeight X (transformHeight X ν) := by
      unfold gaussianTailZeroWeight; positivity
    have hm := mul_le_mul ht hb hgt (by norm_num : (0 : ℝ) ≤ (6 / 5) * 4)
    convert hm using 1 <;> first | rfl | ring
  have hcount := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 2 * zeroCountErrorBound (transformHeight X ν))
  have hc : 8 / optimalWidth X ν^2 * zeroCountErrorBound (transformHeight X ν) *
      gaussianTailZeroWeight X (transformHeight X ν) ≤
        2 * zeroCountErrorBound (transformHeight X ν) * gaussianZeroWeight X (transformHeight X ν) := by
    convert hcount using 1 <;> first | rfl | ring
  have hEh := zeroCountErrorBound_height X ν hX hν hν1
  have hall : 2 * zeroCountErrorBound (transformHeight X ν) * gaussianZeroWeight X (transformHeight X ν) +
      8 / optimalWidth X ν^2 * zeroCountErrorBound (transformHeight X ν) * gaussianTailZeroWeight X (transformHeight X ν) +
      36 / optimalWidth X ν^2 * gaussianCountTailEnvelope X (X * ν) ≤
        4 * (9 * X + 81) * gaussianZeroWeight X (transformHeight X ν) := by
    have hm := mul_le_mul_of_nonneg_right hEh hg
    nlinarith only [htail, hc, hm, hg]
  have hcoef : 4 * Real.pi * (X + 2 * ν) / (X * G0 X ν * ν * transformHeight X ν) ≤
      (257 / 100 : ℝ) * (X + 2) * Real.exp (-X) := by
    have hG := G0_gt_seven_tenths X ν hX hν
    have hs := sqrt_X_gt_289 X hX
    have htseed := transformHeight_seed_lower X ν hX hseed
    have hsX := Real.sq_sqrt hXp.le
    have hπ := Real.pi_lt_d4
    have hGp : 0 < G0 X ν := by linarith
    have hden : 0 < X * G0 X ν * ν * transformHeight X ν := by positivity
    apply (div_le_iff₀ hden).2
    rw [Real.exp_neg]
    rw [show (257 / 100 : ℝ) * (X + 2) * (Real.exp X)⁻¹ *
      (X * G0 X ν * ν * transformHeight X ν) =
      ((257 / 100 : ℝ) * (X + 2) * (X * G0 X ν * ν * transformHeight X ν)) * (Real.exp X)⁻¹ by ring]
    apply (le_mul_inv_iff₀ (Real.exp_pos X)).2
    have hbase : (4 : ℝ) * Real.pi ≤ (257 / 100) * (5 / 2) * (7 / 10) * (97 / 100) * Real.sqrt X := by
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right htseed (Real.sqrt_nonneg X)
    have h2 : (5 / 2 : ℝ) * Real.sqrt X * Real.exp X ≤ X * transformHeight X ν := by
      calc
        (5 / 2 : ℝ) * Real.sqrt X * Real.exp X = (5 / 2 : ℝ) * Real.exp X * Real.sqrt X := by ring
        _ ≤ Real.sqrt X * transformHeight X ν * Real.sqrt X := h1
        _ = (Real.sqrt X)^2 * transformHeight X ν := by ring
        _ = X * transformHeight X ν := by rw [hsX]
    have h3 : (7 / 10 : ℝ) * (97 / 100) ≤ G0 X ν * ν :=
      mul_le_mul hG.le hν.le (by norm_num) (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ X * transformHeight X ν)
    have h5 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (7 / 10) * (97 / 100))
    have h6 := mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ (X + 2) * Real.exp X)
    have h45 : (7 / 10 : ℝ) * (97 / 100) * (X * transformHeight X ν) ≤
        X * G0 X ν * ν * transformHeight X ν := by
      nlinarith only [h4]
    have h7 := mul_le_mul_of_nonneg_left (h5.trans h45)
      (by positivity : 0 ≤ (257 / 100 : ℝ) * (X + 2))
    have h8 := mul_le_mul_of_nonneg_right (show X + 2 * ν ≤ X + 2 by linarith)
      (by positivity : 0 ≤ 4 * Real.pi * Real.exp X)
    nlinarith only [h6, h7, h8]
  have hGn : G0 X ν ≠ 0 := (G0_pos X ν hX hν).ne'
  have hid := low_weight_width_identity X ν hXp.ne' hνp.ne'
  have hD : 0 < X + 2 * ν := by positivity
  have hsave : 0 < optimalWidth X ν * ν / (X + 2 * ν) := by positivity
  have hident : 4 * (9 * X + 81) * gaussianZeroWeight X (transformHeight X ν) =
      (9 * X + 81) * (4 * Real.pi * (X + 2 * ν) / (X * G0 X ν * ν * transformHeight X ν)) *
        (optimalWidth X ν * ν / (X + 2 * ν)) := by
    rw [hid]
    field_simp [hGn]
    <;> ring
  rw [hident] at hall
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ 9 * X + 81)) hsave.le
  have hn := mul_lt_mul_of_pos_right (counting_error_numerical_margin_with_tail X hX) hsave
  apply hall.trans_lt
  exact hm.trans_lt (by convert hn using 1 <;> ring)

end DusartSmoothing


