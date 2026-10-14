-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Construction
-- name    : dusart_psi_433_20261014_Construction
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:35.259346+00:00
-- url     : https://prove2.me/theorems/6b157597-3e16-4507-875d-e71c94a78ab7
-- title:
--   Dusart smoothing: Construction
-- statement:
--   This module gives the complete construction component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Parameters
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DusartSmoothing

noncomputable def G0 (X ν : ℝ) : ℝ :=
  ν ^ 2 * (ν - Real.log (2 * Real.pi) / X)

noncomputable def G1 (X ν : ℝ) : ℝ :=
  ν ^ 2 / (2 * ν ^ 2 - 1) *
    (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X))

noncomputable def Y (X ν : ℝ) : ℝ := X * (1 - ν) ^ 2 / ν

noncomputable def k (X ν : ℝ) : ℝ :=
  X / (2 * Real.pi) * Real.sqrt ((G0 X ν) ^ 3 / G1 X ν) *
    Real.exp (-2 * X * (1 - ν) - Y X ν)

lemma G0_pos (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) : 0 < G0 X ν := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hm : Real.log (2 * Real.pi) < X * ν := by
    have hh := mul_lt_mul_of_pos_right hX hνp
    nlinarith [log_two_pi_bounds.2]
  dsimp [G0]
  exact mul_pos (sq_pos_of_pos hνp) (sub_pos.mpr ((div_lt_iff₀ hXp).2 (by nlinarith)))

lemma G0_lt_one (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : G0 X ν < 1 := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have ha : 0 < Real.log (2 * Real.pi) / X := by
    exact div_pos (by linarith [log_two_pi_bounds.1]) hXp
  have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hνp.le hν1
  have hprod := mul_pos (sq_pos_of_pos hνp) ha
  dsimp [G0]
  nlinarith

lemma G0_lt_G1 (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : G0 X ν < G1 X ν := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hD := (factors_pos X ν hX hν hν1).1
  have hD1 : 2 * ν ^ 2 - 1 ≤ 1 := by nlinarith
  let B := ν ^ 2 * (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X))
  have hdiff : B - G0 X ν = ν ^ 2 / (2 * X) := by
    dsimp [B, G0]
    field_simp
    ring
  have hBG : G0 X ν < B := by
    have hh : 0 < ν ^ 2 / (2 * X) := div_pos (sq_pos_of_pos hνp) (by positivity)
    linarith
  have hBp : 0 < B := (G0_pos X ν hX hν).trans hBG
  have hG1 : G1 X ν = B / (2 * ν ^ 2 - 1) := by
    dsimp [G1, B]
    ring
  have hB1 : B ≤ G1 X ν := by
    rw [hG1]
    apply (le_div_iff₀ hD).2
    exact mul_le_of_le_one_right hBp.le hD1
  exact hBG.trans_le hB1

lemma G1_pos (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : 0 < G1 X ν :=
  (G0_pos X ν hX hν).trans (G0_lt_G1 X ν hX hν hν1)

lemma G_product (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : G0 X ν * G1 X ν = U X ν := by
  have hXp : X ≠ 0 := ne_of_gt (by linarith : 0 < X)
  have hνp : ν ≠ 0 := ne_of_gt (by linarith : 0 < ν)
  have hD := ne_of_gt (factors_pos X ν hX hν hν1).1
  dsimp [G0, G1, U]
  field_simp
  ring

lemma G_ratio_bounds (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) :
    0 < (G0 X ν) ^ 3 / G1 X ν ∧ (G0 X ν) ^ 3 / G1 X ν < 1 := by
  have h0 := G0_pos X ν hX hν
  have h1 := G1_pos X ν hX hν hν1
  have h01 := G0_lt_one X ν hX hν hν1
  have h02 : (G0 X ν) ^ 2 < 1 := pow_lt_one₀ h0.le h01 (by norm_num)
  have h03 : (G0 X ν) ^ 3 < G0 X ν := by
    have hh := mul_lt_mul_of_pos_left h02 h0
    nlinarith only [hh]
  exact ⟨div_pos (pow_pos h0 _) h1,
    (div_lt_one h1).2 (h03.trans (G0_lt_G1 X ν hX hν hν1))⟩

lemma Y_nonneg (X ν : ℝ) (hX : 0 ≤ X) (hν : 0 < ν) : 0 ≤ Y X ν := by
  dsimp [Y]
  positivity

lemma seed_exponential_cancellation (X : ℝ) (hX : 0 < X) :
    X / (2 * Real.pi) * Real.exp (-2 * X * (1 - seed X)) = 1 := by
  have harg : 0 < X / (2 * Real.pi) := div_pos hX (by positivity)
  have hid : -2 * X * (1 - seed X) = -Real.log (X / (2 * Real.pi)) := by
    dsimp [seed]
    field_simp
    ring
  rw [hid, Real.exp_neg, Real.exp_log harg]
  exact mul_inv_cancel₀ (ne_of_gt harg)

lemma k_seed_lt_one (X : ℝ) (hX : (836 / 100 : ℝ) < X) : k X (seed X) < 1 := by
  have hs := seed_bounds X hX
  have hXp : 0 < X := by linarith
  have hνp : 0 < seed X := by linarith
  have hr := G_ratio_bounds X (seed X) hX hs.1 hs.2.le
  have hsr : Real.sqrt ((G0 X (seed X)) ^ 3 / G1 X (seed X)) < 1 :=
    (Real.sqrt_lt hr.1.le (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hr.2)
  have he : Real.exp (-Y X (seed X)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Y_nonneg X (seed X) hXp.le hνp])
  have hid : k X (seed X) =
      Real.sqrt ((G0 X (seed X)) ^ 3 / G1 X (seed X)) * Real.exp (-Y X (seed X)) := by
    dsimp [k]
    rw [sub_eq_add_neg, Real.exp_add]
    calc
      _ = (X / (2 * Real.pi) * Real.exp (-2 * X * (1 - seed X))) *
          Real.sqrt ((G0 X (seed X)) ^ 3 / G1 X (seed X)) * Real.exp (-Y X (seed X)) := by ring
      _ = _ := by rw [seed_exponential_cancellation X hXp]; ring
  rw [hid]
  exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) he).trans_lt hsr

lemma log_two_pi_upper : Real.log (2 * Real.pi) < (1838 / 1000 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (1838 / 1000 : ℝ)) 11
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  apply (Real.log_lt_iff_lt_exp (by positivity)).2
  linarith [Real.pi_lt_d4]

lemma k_one_square (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    (k X 1) ^ 2 =
      (X - Real.log (2 * Real.pi)) ^ 3 /
        (4 * Real.pi ^ 2 * (X - Real.log (2 * Real.pi) + 1 / 2)) := by
  have hXp : X ≠ 0 := ne_of_gt (by linarith : 0 < X)
  have h1 := G1_pos X 1 hX (by norm_num) (by norm_num)
  have hr := (G_ratio_bounds X 1 hX (by norm_num) (by norm_num)).1
  have ha := log_two_pi_bounds
  have hD : X - Real.log (2 * Real.pi) + 1 / 2 ≠ 0 := ne_of_gt (by linarith)
  have hs := Real.sq_sqrt hr.le
  norm_num [k, Y] at hs ⊢
  rw [mul_pow, div_pow, hs]
  dsimp [G0, G1]
  field_simp
  ring

lemma k_one_gt_one (X : ℝ) (hX : (836 / 100 : ℝ) < X) : 1 < k X 1 := by
  let z := X - Real.log (2 * Real.pi)
  let c : ℝ := 6522 / 1000
  have hz : c < z := by dsimp [z, c]; linarith [log_two_pi_upper]
  have hπ := Real.pi_lt_d4
  have hπ2 : Real.pi ^ 2 < (31416 / 10000 : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
  have hc : 0 < c := by norm_num [c]
  have hzpos : 0 < z := hc.trans hz
  have hbase : 0 < c ^ 3 - 4 * Real.pi ^ 2 * c - 2 * Real.pi ^ 2 := by
    dsimp [c] at *
    nlinarith
  have hcoef : 0 < z ^ 2 + z * c + c ^ 2 - 4 * Real.pi ^ 2 := by
    have hzc := mul_lt_mul_of_pos_right hz hc
    dsimp [c] at *
    nlinarith
  have hpoly : 0 < z ^ 3 - 4 * Real.pi ^ 2 * z - 2 * Real.pi ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hz) hcoef
    have hid : z ^ 3 - 4 * Real.pi ^ 2 * z - 2 * Real.pi ^ 2 =
        (z - c) * (z ^ 2 + z * c + c ^ 2 - 4 * Real.pi ^ 2) +
          (c ^ 3 - 4 * Real.pi ^ 2 * c - 2 * Real.pi ^ 2) := by ring
    rw [hid]
    linarith
  have hden : 0 < 4 * Real.pi ^ 2 * (z + 1 / 2) := by positivity
  have hs : 1 < (k X 1) ^ 2 := by
    rw [k_one_square X hX]
    change 1 < z ^ 3 / (4 * Real.pi ^ 2 * (z + 1 / 2))
    apply (one_lt_div hden).2
    nlinarith
  have hp : 0 ≤ k X 1 := by
    dsimp [k]
    positivity
  nlinarith

lemma continuousOn_k (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    ContinuousOn (k X) (Set.Icc (seed X) 1) := by
  have hs := seed_bounds X hX
  intro ν hν
  have hν97 : (97 / 100 : ℝ) < ν := hs.1.trans_le hν.1
  have hνp : ν ≠ 0 := ne_of_gt (by linarith : 0 < ν)
  have hD : 2 * ν ^ 2 - 1 ≠ 0 := ne_of_gt (factors_pos X ν hX hν97 hν.2).1
  have hG : ν ^ 2 / (2 * ν ^ 2 - 1) *
      (ν + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)) ≠ 0 :=
    ne_of_gt (G1_pos X ν hX hν97 hν.2)
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun t : ℝ => X / (2 * Real.pi) *
    Real.sqrt ((t ^ 2 * (t - Real.log (2 * Real.pi) / X)) ^ 3 /
      (t ^ 2 / (2 * t ^ 2 - 1) *
        (t + (1 - 2 * Real.log (2 * Real.pi)) / (2 * X)))) *
      Real.exp (-2 * X * (1 - t) - X * (1 - t) ^ 2 / t)) ν
  fun_prop (disch := assumption)

theorem exists_optimal_smoothing_parameter (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧ seed X < ν ∧ k X ν = 1 := by
  have hs := seed_bounds X hX
  obtain ⟨ν, hν, hkν⟩ :=
    (intermediate_value_Icc hs.2.le (continuousOn_k X hX))
      ⟨(k_seed_lt_one X hX).le, (k_one_gt_one X hX).le⟩
  have hνseed : seed X < ν := by
    by_contra hh
    have heq : ν = seed X := le_antisymm (le_of_not_gt hh) hν.1
    rw [heq] at hkν
    have hb := k_seed_lt_one X hX
    linarith
  have hν1 : ν < 1 := by
    by_contra hh
    have heq : ν = 1 := le_antisymm hν.2 (le_of_not_gt hh)
    rw [heq] at hkν
    have hb := k_one_gt_one X hX
    linarith
  exact ⟨ν, hs.1.trans hνseed, hν1, hνseed, hkν⟩

end DusartSmoothing


