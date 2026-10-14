-- Prove2me | Definitions.Def_dusart_psi_433_20261014_FactorBounds
-- name    : dusart_psi_433_20261014_FactorBounds
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:07.886016+00:00
-- url     : https://prove2.me/theorems/1711e972-6fc4-4587-ba98-c42c7fa288f2
-- title:
--   Dusart smoothing: Factor Bounds
-- statement:
--   This module gives the complete factor bounds component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Balance
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DusartSmoothing

lemma sixth_power_ratio_lower (ν : ℝ) (hν : (97 / 100 : ℝ) < ν) :
    (97 / 100 : ℝ) ^ 6 / (2 * (97 / 100 : ℝ) ^ 2 - 1) ≤
      ν ^ 6 / (2 * ν ^ 2 - 1) := by
  have hνp : 0 < ν := by linarith
  have hν₂ : (97 / 100 : ℝ) ^ 2 ≤ ν ^ 2 := by nlinarith
  have hD : 0 < 2 * ν ^ 2 - 1 := by nlinarith
  apply (div_le_div_iff₀ (by norm_num : 0 < 2 * (97 / 100 : ℝ) ^ 2 - 1) hD).2
  let c : ℝ := (97 / 100 : ℝ) ^ 2
  have hc : 0 < c := by norm_num [c]
  have hq : c ≤ ν ^ 2 := hν₂
  have hq₂ : c ^ 2 ≤ ν ^ 4 := by nlinarith only [hq, hc, sq_nonneg (ν ^ 2 - c)]
  have hqc : c ^ 2 ≤ ν ^ 2 * c := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) hc.le]
  have hcoef : 0 ≤ (2 * c - 1) * (ν ^ 4 + ν ^ 2 * c + c ^ 2) - 2 * c ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left (show 3 * c ^ 2 ≤ ν ^ 4 + ν ^ 2 * c + c ^ 2 by linarith)
      (show 0 ≤ 2 * c - 1 by norm_num [c])
    norm_num [c] at hm ⊢
    linarith
  have hp := mul_nonneg (sub_nonneg.mpr hq) hcoef
  have hid : ν ^ 6 * (2 * c - 1) - c ^ 3 * (2 * ν ^ 2 - 1) =
      (ν ^ 2 - c) * ((2 * c - 1) * (ν ^ 4 + ν ^ 2 * c + c ^ 2) - 2 * c ^ 3) := by ring
  have hz : 0 ≤ ν ^ 6 * (2 * c - 1) - c ^ 3 * (2 * ν ^ 2 - 1) := by rw [hid]; exact hp
  dsimp [c] at hz
  nlinarith only [hz]

lemma sixth_power_ratio_le_one (ν : ℝ) (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) :
    ν ^ 6 / (2 * ν ^ 2 - 1) ≤ 1 := by
  have hνp : 0 < ν := by linarith
  have hν₂ : (97 / 100 : ℝ) ^ 2 ≤ ν ^ 2 := by nlinarith
  have hν₂1 : ν ^ 2 ≤ 1 := pow_le_one₀ hνp.le hν1
  have hD : 0 < 2 * ν ^ 2 - 1 := by nlinarith
  apply (div_le_one hD).2
  have hc : 0 ≤ ν ^ 4 + ν ^ 2 - 1 := by nlinarith [sq_nonneg (ν ^ 2)]
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hν₂1) hc
  have hid : ν ^ 6 - (2 * ν ^ 2 - 1) = (ν ^ 2 - 1) * (ν ^ 4 + ν ^ 2 - 1) := by ring
  linarith only [hp, hid]

lemma log_two_pi_upper_precise : Real.log (2 * Real.pi) < (18379 / 10000 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (18379 / 10000 : ℝ)) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  apply (Real.log_lt_iff_lt_exp (by positivity)).2
  linarith [Real.pi_lt_d4]

theorem U_gt_sixty_one_percent (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (_hν1 : ν ≤ 1) : (61 / 100 : ℝ) < U X ν := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hXν : (836 / 100 : ℝ) * (97 / 100) < X * ν := by
    have hh := mul_lt_mul_of_pos_right hX hνp
    nlinarith
  have hXνp : 0 < X * ν := mul_pos hXp hνp
  let b : ℝ := (836 / 100 : ℝ) * (97 / 100)
  let a : ℝ := 18379 / 10000
  have hb : 0 < b := by norm_num [b]
  have ha : Real.log (2 * Real.pi) < a := log_two_pi_upper_precise
  have hf₁ : 1 - (a - 1 / 2) / b ≤
      1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν) := by
    apply sub_le_sub_left
    apply (div_le_div_iff₀ hXνp hb).2
    have hm := mul_le_mul_of_nonneg_left (show b ≤ X * ν by exact hXν.le)
      (show 0 ≤ a - 1 / 2 by norm_num [a])
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right ha.le (1 / 2)) hb.le).trans hm
  have hf₂ : 1 - a / b ≤ 1 - Real.log (2 * Real.pi) / (X * ν) := by
    apply sub_le_sub_left
    apply (div_le_div_iff₀ hXνp hb).2
    have hm := mul_le_mul_of_nonneg_left (show b ≤ X * ν by exact hXν.le)
      (show 0 ≤ a by norm_num [a])
    have hh := mul_lt_mul_of_pos_right ha hb
    nlinarith only [hm, hh]
  have hF := sixth_power_ratio_lower ν hν
  have h₁ : 0 ≤ 1 - (a - 1 / 2) / b := by norm_num [a, b]
  have h₂ : 0 ≤ 1 - a / b := by norm_num [a, b]
  have hF₀ : 0 ≤ (97 / 100 : ℝ) ^ 6 / (2 * (97 / 100 : ℝ) ^ 2 - 1) := by norm_num
  have hm := mul_le_mul
    (mul_le_mul hF hf₁ h₁ (hF₀.trans hF)) hf₂ h₂
    (mul_nonneg (hF₀.trans hF) (h₁.trans hf₁))
  have hbase : (61 / 100 : ℝ) <
      (97 / 100 : ℝ) ^ 6 / (2 * (97 / 100 : ℝ) ^ 2 - 1) *
        (1 - (a - 1 / 2) / b) * (1 - a / b) := by norm_num [a, b]
  exact hbase.trans_le hm

theorem U_lt_one (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : U X ν < 1 := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hf := factors_pos X ν hX hν hν1
  have hF := sixth_power_ratio_le_one ν hν hν1
  have hFpos : 0 ≤ ν ^ 6 / (2 * ν ^ 2 - 1) :=
    div_nonneg (pow_nonneg hνp.le _) hf.1.le
  have h₁ : 1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν) ≤ 1 := by
    have hp : 0 ≤ (Real.log (2 * Real.pi) - 1 / 2) / (X * ν) :=
      div_nonneg (by linarith [log_two_pi_bounds.1]) (mul_pos hXp hνp).le
    linarith
  have h₂ : 1 - Real.log (2 * Real.pi) / (X * ν) < 1 := by
    have hp : 0 < Real.log (2 * Real.pi) / (X * ν) :=
      div_pos (by linarith [log_two_pi_bounds.1]) (mul_pos hXp hνp)
    linarith
  have hm : ν ^ 6 / (2 * ν ^ 2 - 1) *
      (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) ≤ 1 :=
    (mul_le_of_le_one_right hFpos h₁).trans hF
  dsimp [U]
  exact (mul_le_mul_of_nonneg_right hm hf.2.2.le).trans_lt (by simpa using h₂)

end DusartSmoothing


