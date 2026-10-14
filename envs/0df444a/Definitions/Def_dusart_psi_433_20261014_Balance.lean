-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Balance
-- name    : dusart_psi_433_20261014_Balance
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:09.546689+00:00
-- url     : https://prove2.me/theorems/d5e793db-4467-43ca-9221-c8c91d7a1c12
-- title:
--   Dusart smoothing: Balance
-- statement:
--   This module gives the complete balance component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_KernelIntegrals
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DusartSmoothing

noncomputable def balanceCoefficient (X ν : ℝ) : ℝ :=
  X / (2 * Real.pi) * Real.exp (-2 * X - Y X ν)

noncomputable def transformHeight (X ν : ℝ) : ℝ := Real.exp (X * ν)

noncomputable def optimalWidth (X ν : ℝ) : ℝ :=
  2 * balanceCoefficient X ν * G0 X ν * transformHeight X ν

lemma balanceCoefficient_pos (X ν : ℝ) (hX : 0 < X) :
    0 < balanceCoefficient X ν := by
  dsimp [balanceCoefficient]
  positivity

lemma transformHeight_pos (X ν : ℝ) : 0 < transformHeight X ν := Real.exp_pos _

lemma optimalWidth_pos (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) : 0 < optimalWidth X ν := by
  have hc := balanceCoefficient_pos X ν (show 0 < X by linarith)
  have hG := G0_pos X ν hX hν
  have hT := transformHeight_pos X ν
  dsimp [optimalWidth]
  positivity

lemma k_balance_form (X ν : ℝ) :
    k X ν = balanceCoefficient X ν * transformHeight X ν ^ 2 *
      Real.sqrt (G0 X ν ^ 3 / G1 X ν) := by
  dsimp [k, balanceCoefficient, transformHeight]
  rw [← Real.exp_nat_mul]
  have he : Real.exp (-2 * X - Y X ν) * Real.exp ((2 : ℕ) * (X * ν)) =
      Real.exp (-2 * X * (1 - ν) - Y X ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = X / (2 * Real.pi) *
        (Real.exp (-2 * X - Y X ν) * Real.exp ((2 : ℕ) * (X * ν))) *
          Real.sqrt (G0 X ν ^ 3 / G1 X ν) := by rw [he]; ring
    _ = _ := by ring

lemma balance_square_identity (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    balanceCoefficient X ν ^ 2 * transformHeight X ν ^ 4 * G0 X ν ^ 3 =
      G1 X ν := by
  have h1 := G1_pos X ν hX hν hν1
  have hr := (G_ratio_bounds X ν hX hν hν1).1
  have hs := congrArg (fun z : ℝ => z ^ 2) hk
  rw [k_balance_form, mul_pow, mul_pow, Real.sq_sqrt hr.le] at hs
  norm_num at hs
  apply (div_eq_one_iff_eq (ne_of_gt h1)).1
  calc
    _ = balanceCoefficient X ν ^ 2 * (transformHeight X ν ^ 2) ^ 2 *
        (G0 X ν ^ 3 / G1 X ν) := by ring
    _ = 1 := hs

lemma optimalWidth_balances (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    optimalWidth X ν ^ 2 * transformHeight X ν ^ 2 * G0 X ν = 4 * G1 X ν := by
  have hs := balance_square_identity X ν hX hν hν1 hk
  dsimp [optimalWidth]
  nlinarith only [hs]

lemma balanced_kernel_sum (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    balanceCoefficient X ν *
      (G0 X ν * transformHeight X ν +
        4 * G1 X ν / (optimalWidth X ν ^ 2 * transformHeight X ν)) =
      optimalWidth X ν := by
  have hδ := (optimalWidth_pos X ν hX hν).ne'
  have hT := (transformHeight_pos X ν).ne'
  have hs := optimalWidth_balances X ν hX hν hν1 hk
  have he : 4 * G1 X ν / (optimalWidth X ν ^ 2 * transformHeight X ν) =
      G0 X ν * transformHeight X ν := by
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 hδ) hT)).2
    nlinarith only [hs]
  rw [he]
  dsimp [optimalWidth]
  ring

lemma lower_exponential_identity (X ν : ℝ) (hν : ν ≠ 0) :
    Real.exp (-X / ν) = Real.exp (-2 * X - Y X ν) * transformHeight X ν := by
  dsimp [transformHeight]
  rw [← Real.exp_add]
  congr 1
  dsimp [Y]
  field_simp
  ring

lemma upper_exponential_identity (X ν : ℝ) (hν : ν ≠ 0) :
    Real.exp (-(2 * ν + 1 / ν) * X) =
      Real.exp (-2 * X - Y X ν) / transformHeight X ν := by
  dsimp [transformHeight]
  rw [← Real.exp_sub]
  congr 1
  dsimp [Y]
  field_simp
  ring

theorem balanced_kernel_envelopes (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    (lowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) +
      4 / optimalWidth X ν ^ 2 *
        upperEnvelope X (Real.log (2 * Real.pi)) (X * ν)) / (2 * Real.pi) =
      optimalWidth X ν := by
  have hXp : X ≠ 0 := ne_of_gt (by linarith : 0 < X)
  have hνp : ν ≠ 0 := ne_of_gt (by linarith : 0 < ν)
  have hD := (factors_pos X ν hX hν hν1).1.ne'
  rw [lowerEnvelope_at_parameter X ν hXp hνp,
    upperEnvelope_at_parameter X ν hXp hνp hD,
    lower_exponential_identity X ν hνp, upper_exponential_identity X ν hνp]
  calc
    _ = balanceCoefficient X ν *
        (G0 X ν * transformHeight X ν +
          4 * G1 X ν / (optimalWidth X ν ^ 2 * transformHeight X ν)) := by
      dsimp [balanceCoefficient]
      ring
    _ = optimalWidth X ν := balanced_kernel_sum X ν hX hν hν1 hk

lemma optimalWidth_square (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    optimalWidth X ν ^ 2 =
      4 * balanceCoefficient X ν * Real.sqrt (U X ν) := by
  have h0 := G0_pos X ν hX hν
  have h1 := G1_pos X ν hX hν hν1
  have hr := (G_ratio_bounds X ν hX hν hν1).1
  have hu := U_pos X ν hX hν hν1
  have hp : (Real.sqrt (G0 X ν ^ 3 / G1 X ν) * Real.sqrt (U X ν)) ^ 2 =
      (G0 X ν ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr.le, Real.sq_sqrt hu.le, ← G_product X ν hX hν hν1]
    field_simp
    try ring
  have he : Real.sqrt (G0 X ν ^ 3 / G1 X ν) * Real.sqrt (U X ν) = G0 X ν ^ 2 := by
    have hsp : 0 ≤ Real.sqrt (G0 X ν ^ 3 / G1 X ν) * Real.sqrt (U X ν) := by positivity
    nlinarith only [hp, hsp, sq_nonneg (G0 X ν)]
  have hk' := hk
  rw [k_balance_form] at hk'
  have hh := congrArg (fun z : ℝ => z * Real.sqrt (U X ν)) hk'
  rw [mul_assoc, he, one_mul] at hh
  dsimp [optimalWidth]
  calc
    _ = 4 * balanceCoefficient X ν *
        (balanceCoefficient X ν * transformHeight X ν ^ 2 * G0 X ν ^ 2) := by ring
    _ = _ := by rw [hh]

theorem optimalWidth_formula (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    optimalWidth X ν =
      Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
        Real.exp (-Y X ν / 2) * Real.sqrt X * Real.exp (-X) := by
  have hXp : 0 < X := by linarith
  have hu := U_pos X ν hX hν hν1
  have hpi : 0 ≤ 2 / Real.pi := by positivity
  have he : Real.exp (-Y X ν / 2) ^ 2 * Real.exp (-X) ^ 2 =
      Real.exp (-2 * X - Y X ν) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hr : (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
        Real.exp (-Y X ν / 2) * Real.sqrt X * Real.exp (-X)) ^ 2 =
      4 * balanceCoefficient X ν * Real.sqrt (U X ν) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hpi,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hXp.le]
    calc
      _ = 2 / Real.pi * Real.sqrt (U X ν) * X *
          (Real.exp (-Y X ν / 2) ^ 2 * Real.exp (-X) ^ 2) := by ring
      _ = _ := by rw [he]; dsimp [balanceCoefficient]; ring
  have hl := optimalWidth_square X ν hX hν hν1 hk
  have hδ := optimalWidth_pos X ν hX hν
  have hs : 0 ≤ Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
        Real.exp (-Y X ν / 2) * Real.sqrt X * Real.exp (-X) := by positivity
  nlinarith only [hl, hr, hδ, hs]

theorem optimalWidth_fourth_root_bound (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    2 * optimalWidth X ν ≤ Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (U X ν)) * Real.sqrt X * Real.exp (-X) := by
  have hXp : 0 ≤ X := by linarith
  have hνp : 0 < ν := by linarith
  have he : Real.exp (-Y X ν / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Y_nonneg X ν hXp hνp])
  have hs : 2 * Real.sqrt (2 / Real.pi) = Real.sqrt (8 / Real.pi) := by
    have hs₂ := Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi)
    have hs₈ := Real.sq_sqrt (by positivity : 0 ≤ 8 / Real.pi)
    have hid : (8 / Real.pi : ℝ) = 4 * (2 / Real.pi) := by ring
    have hs₈' : Real.sqrt (8 / Real.pi) ^ 2 = 4 * (2 / Real.pi) := hs₈.trans hid
    nlinarith only [hs₂, hs₈', Real.sqrt_nonneg (2 / Real.pi),
      Real.sqrt_nonneg (8 / Real.pi)]
  rw [optimalWidth_formula X ν hX hν hν1 hk]
  calc
    _ = (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
        Real.sqrt X * Real.exp (-X)) * Real.exp (-Y X ν / 2) := by ring
    _ ≤ _ := by rw [← hs]; exact mul_le_of_le_one_right (by positivity) he

theorem balanced_integral_bound (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hk : k X ν = 1) :
    ((∫ u in Real.log (2 * Real.pi)..X * ν,
        (u - Real.log (2 * Real.pi)) * Real.exp (-X ^ 2 / u)) +
      4 / optimalWidth X ν ^ 2 *
        (∫ u in Set.Ioi (X * ν),
          (u - Real.log (2 * Real.pi)) * Real.exp (-2 * u + (-X ^ 2 / u)))) /
        (2 * Real.pi) ≤ optimalWidth X ν := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hu₀ : 0 < X * ν := mul_pos hXp hνp
  have ha : Real.log (2 * Real.pi) ≤ X * ν := by
    have hm := mul_lt_mul_of_pos_right hX hνp
    nlinarith [log_two_pi_bounds.2]
  have ha' : 2 * Real.log (2 * Real.pi) - 1 ≤ X * ν := by
    have hm := mul_lt_mul_of_pos_right hX hνp
    nlinarith [log_two_pi_bounds.2]
  have hD : 0 < 2 * (X * ν) ^ 2 - X ^ 2 := by
    have hp := mul_pos (sq_pos_of_pos hXp) (factors_pos X ν hX hν hν1).1
    nlinarith only [hp]
  have hl := lower_kernel_integral_bound X (Real.log (2 * Real.pi))
    (Real.log (2 * Real.pi)) (X * ν) hXp
      (by linarith [log_two_pi_bounds.1]) le_rfl ha
  have hu := upper_kernel_improper_integral_bound X (Real.log (2 * Real.pi))
    (X * ν) hu₀ ha ha' hD
  have hh := add_le_add hl (mul_le_mul_of_nonneg_left hu
    (by positivity : 0 ≤ 4 / optimalWidth X ν ^ 2))
  exact ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).2 hh).trans_eq
    (balanced_kernel_envelopes X ν hX hν hν1 hk)

theorem exists_balanced_integral_parameter (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    ∃ ν δ : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧ 0 < δ ∧
      ((∫ u in Real.log (2 * Real.pi)..X * ν,
          (u - Real.log (2 * Real.pi)) * Real.exp (-X ^ 2 / u)) +
        4 / δ ^ 2 *
          (∫ u in Set.Ioi (X * ν),
            (u - Real.log (2 * Real.pi)) * Real.exp (-2 * u + (-X ^ 2 / u)))) /
          (2 * Real.pi) ≤ δ ∧
      2 * δ ≤ Real.sqrt (8 / Real.pi) * Real.sqrt (Real.sqrt (U X ν)) *
        Real.sqrt X * Real.exp (-X) := by
  obtain ⟨ν, hν, hν1, hνseed, hk⟩ := exists_optimal_smoothing_parameter X hX
  refine ⟨ν, optimalWidth X ν, hν, hν1, optimalWidth_pos X ν hX hν, ?_, ?_⟩
  · exact balanced_integral_bound X ν hX hν hν1.le hk
  · exact optimalWidth_fourth_root_bound X ν hX hν hν1.le hk

end DusartSmoothing


