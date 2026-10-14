-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ReflectionAbsorption
-- name    : dusart_psi_433_20261014_ReflectionAbsorption
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:44:41.914119+00:00
-- url     : https://prove2.me/theorems/2d43a1cf-4797-40c4-a157-0a718cbf6459
-- title:
--   Dusart smoothing: Reflection Absorption
-- statement:
--   This module gives the complete reflection absorption component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WidthElementary
import Definitions.Def_dusart_psi_433_20261014_HeightBounds
noncomputable section
namespace DusartSmoothing
open Real

lemma reflection_loss_absorbed (X ν q : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1)
    (hq : 0 ≤ q) (hqb : q ≤ Real.exp (-4 * X)) :
    q * (32 * transformHeight X ν + 48 / optimalWidth X ν^2) <
      (2 / 100 : ℝ) * (optimalWidth X ν * ν / (X + 2 * ν)) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hδ := optimalWidth_pos X ν hX hν
  have hT := transformHeight_pos X ν
  have hD : 0 < X + 2 * ν := by positivity
  have hb := balanced_width_height_ge_two X ν hX hν hν1 hk
  have hb2 : 4 ≤ optimalWidth X ν^2 * transformHeight X ν^2 := by nlinarith
  have hi : 48 / optimalWidth X ν^2 ≤ 12 * transformHeight X ν^2 :=
    (div_le_iff₀ (sq_pos_of_pos hδ)).2 (by nlinarith only [hb2])
  have hC : q * (32 * transformHeight X ν + 48 / optimalWidth X ν^2) ≤
      (32 * transformHeight X ν + 12 * transformHeight X ν^2) * Real.exp (-4 * X) := by
    have hm := mul_le_mul hqb (add_le_add le_rfl hi)
      (by positivity : 0 ≤ 32 * transformHeight X ν + 48 / optimalWidth X ν^2)
      (Real.exp_nonneg (-4 * X))
    convert hm using 1 <;> first | rfl | ring
  have hTex : transformHeight X ν ≤ Real.exp X := by
    unfold transformHeight
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hXp.le (sub_nonneg.mpr hν1)]
  have hT2 := pow_le_pow_left₀ hT.le hTex 2
  have hT3 := pow_le_pow_left₀ hT.le hTex 3
  have he2 : Real.exp X^2 * Real.exp (-4 * X) = Real.exp (-2 * X) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1 <;> norm_num <;> ring
  have he3 : Real.exp X^3 * Real.exp (-4 * X) = Real.exp (-X) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1 <;> norm_num <;> ring
  have hm : (16 * transformHeight X ν^2 + 6 * transformHeight X ν^3) * Real.exp (-4 * X) ≤
      16 * Real.exp (-2 * X) + 6 * Real.exp (-X) := by
    have h := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hT2 (by norm_num : (0 : ℝ) ≤ 16))
        (mul_le_mul_of_nonneg_left hT3 (by norm_num : (0 : ℝ) ≤ 6))) (Real.exp_nonneg (-4 * X))
    simpa only [add_mul, mul_assoc, he2, he3] using h
  have hnum := (div_lt_iff₀ hνp).1 (reflection_numerical_margin X ν hX hν)
  have hmd : (16 * transformHeight X ν^2 + 6 * transformHeight X ν^3) * Real.exp (-4 * X) *
      (X + 2 * ν) < (2 / 100 : ℝ) * ν := by
    have h := mul_le_mul hm (show X + 2 * ν ≤ X + 2 by linarith) hD.le
      (by positivity : 0 ≤ 16 * Real.exp (-2 * X) + 6 * Real.exp (-X))
    exact h.trans_lt hnum
  apply hC.trans_lt
  rw [show (2 / 100 : ℝ) * (optimalWidth X ν * ν / (X + 2 * ν)) =
    ((2 / 100 : ℝ) * optimalWidth X ν * ν) / (X + 2 * ν) by ring]
  apply (lt_div_iff₀ hD).2
  apply (mul_lt_mul_iff_right₀ hT).1
  have hbν := mul_le_mul_of_nonneg_right hb hνp.le
  nlinarith only [hmd, hbν]

end DusartSmoothing


