-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PerronLoss
-- name    : dusart_psi_433_20261014_PerronLoss
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:44:48.760212+00:00
-- url     : https://prove2.me/theorems/759e41bf-262b-42ef-b911-701e8163eb4e
-- title:
--   Dusart smoothing: Perron Loss
-- statement:
--   This module gives the complete perron loss component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_HeightBounds
import Definitions.Def_dusart_psi_433_20261014_WidthSmall
noncomputable section
namespace DusartSmoothing
open Real

lemma elementary_perron_loss_absorbed (X ν x : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1)
    (hx : Real.exp (8 * X) ≤ x) :
    2 + 2048 / optimalWidth X ν^2 <
      optimalWidth X ν * x * (Real.sqrt X * Real.exp (-X)) := by
  have hXp : 0 < X := by linarith
  have hδ := optimalWidth_pos X ν hX hν
  have hxp : 0 < x := (Real.exp_pos _).trans_le hx
  have hb := balanced_width_exp_lower X ν hX hν hν1 hk
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg X)
  have he : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
  have hδe : 2 ≤ optimalWidth X ν * Real.exp X := by nlinarith only [hm, he]
  have he2 : Real.exp (2 * X) = Real.exp X^2 := by
    rw [← Real.exp_nat_mul]; congr 1 <;> norm_num
  have hs : 4 ≤ optimalWidth X ν^2 * Real.exp (2 * X) := by rw [he2]; nlinarith only [hδe]
  have hi : 2048 / optimalWidth X ν^2 ≤ 512 * Real.exp (2 * X) :=
    (div_le_iff₀ (sq_pos_of_pos hδ)).2 (by nlinarith only [hs])
  have h1 : 1 ≤ Real.exp (2 * X) := Real.one_le_exp_iff.mpr (by positivity)
  have hl : 2 + 2048 / optimalWidth X ν^2 ≤ 514 * Real.exp (2 * X) := by linarith
  have h6 : 2 * Real.sqrt X * Real.exp (6 * X) ≤
      optimalWidth X ν * x * (Real.sqrt X * Real.exp (-X)) := by
    have hprod := mul_le_mul hb hx (Real.exp_nonneg (8 * X)) hδ.le
    have hm := mul_le_mul_of_nonneg_right hprod
      (by positivity : 0 ≤ Real.sqrt X * Real.exp (-X))
    have he6 : Real.exp (-X) * Real.exp (8 * X) * Real.exp (-X) = Real.exp (6 * X) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hlhs : (2 * Real.exp (-X) * Real.exp (8 * X)) * (Real.sqrt X * Real.exp (-X)) =
        2 * Real.sqrt X * Real.exp (6 * X) := by
      calc
        _ = 2 * Real.sqrt X * (Real.exp (-X) * Real.exp (8 * X) * Real.exp (-X)) := by ring
        _ = _ := by rw [he6]
    rwa [hlhs] at hm
  have h4 : (4262 : ℝ) < Real.exp (4 * X) :=
    exp_threshold_lower.trans (Real.exp_lt_exp.mpr (by linarith))
  have hsqrt := sqrt_X_gt_289 X hX
  have hnum : (514 : ℝ) < 2 * Real.sqrt X * Real.exp (4 * X) := by
    have hh := mul_le_mul (show (2 : ℝ) ≤ Real.sqrt X by linarith) h4.le (by norm_num)
      (by positivity : (0 : ℝ) ≤ Real.sqrt X)
    nlinarith
  have hm := mul_lt_mul_of_pos_right hnum (Real.exp_pos (2 * X))
  have he6 : Real.exp (4 * X) * Real.exp (2 * X) = Real.exp (6 * X) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [mul_assoc, he6] at hm
  exact hl.trans_lt (hm.trans_le h6)

lemma smoothing_perron_remainder_le (x δ a : ℝ) (hx : 1 ≤ x) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / 2 : ℝ)) (ha : 1 ≤ a) (hab : a + 2 * (δ * x) ≤ x * (1 + 2 * δ)) :
    512 * (a + 2 * (δ * x)) ^ (3 / 2 : ℝ) / (δ * x)^2 ≤ 2048 / δ^2 := by
  have hxp : 0 < x := by linarith
  have hh : 1 ≤ a + 2 * (δ * x) := by linarith [mul_pos hδ hxp]
  have hu : a + 2 * (δ * x) ≤ 2 * x := by
    have hm := mul_le_mul_of_nonneg_left (show 1 + 2 * δ ≤ (2 : ℝ) by linarith) hxp.le
    exact hab.trans (by nlinarith only [hm])
  have hp : (a + 2 * (δ * x)) ^ (3 / 2 : ℝ) ≤ 4 * x^2 := by
    calc
      _ ≤ (a + 2 * (δ * x)) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh (by norm_num)
      _ = (a + 2 * (δ * x))^2 := Real.rpow_two _
      _ ≤ (2 * x)^2 := by gcongr
      _ = 4 * x^2 := by ring
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤ 512)) (sq_nonneg (δ * x))
  have he : 512 * (4 * x^2) / (δ * x)^2 = 2048 / δ^2 := by field_simp [hxp.ne'] <;> ring
  rwa [he] at hm

end DusartSmoothing


