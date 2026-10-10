-- Prove2me | solution 1 for ActuarialValuation.gamblerBoundedRuin_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:57:43.704551+00:00
-- url     : https://prove2.me/submissions/de34a8a0-ad4b-4892-b66b-50bf9ec95cea

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerFairSuccess
import Definitions.Def_actuarial_gamblerOddsRatio
import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerFiniteSuccess
import Definitions.Def_actuarial_gamblerFiniteRuin
import Theorems.Thm_ActuarialValuation_gamblerFiniteSuccess_nonneg
import Theorems.Thm_ActuarialValuation_gamblerFiniteRuin_nonneg
import Theorems.Thm_ActuarialValuation_gamblerFiniteSuccessRuin_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N i n : ℕ) (p : ℝ)
    (hlo : 0 < i) (hhi : i < N)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
    (gamblerFairSuccess N i =
      ((1 / 2 : ℝ) * gamblerFairSuccess N (i + 1)) +
      ((1 / 2 : ℝ) * gamblerFairSuccess N (i - 1))) ∧
    (gamblerBiasedSuccess N i p =
      p * gamblerBiasedSuccess N (i + 1) p +
        (1 - p) * gamblerBiasedSuccess N (i - 1) p) ∧
    (0 ≤ gamblerFiniteSuccess N p n i ∧
      0 ≤ gamblerFiniteRuin N p n i ∧
      gamblerFiniteSuccess N p n i + gamblerFiniteRuin N p n i ≤ 1) := by
  have hf : gamblerFairSuccess N i =
      ((1 / 2 : ℝ) * gamblerFairSuccess N (i + 1)) +
      ((1 / 2 : ℝ) * gamblerFairSuccess N (i - 1)) := by
    have hN : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans hlo hhi))
    have hle : 1 ≤ i := hlo
    have hs : i - 1 + 1 = i := Nat.sub_add_cancel hle
    have hc : (((i - 1 : ℕ) : ℝ) + 1) = (i : ℝ) := by
      have hh := congrArg (fun k : ℕ => (k : ℝ)) hs
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    have hminus : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by linarith [hc]
    unfold gamblerFairSuccess
    rw [hminus, Nat.cast_add, Nat.cast_one]
    field_simp [hN] <;> ring
  have hp : p ≠ 0 := ne_of_gt hp0
  have hb : gamblerBiasedSuccess N i p =
      p * gamblerBiasedSuccess N (i + 1) p +
        (1 - p) * gamblerBiasedSuccess N (i - 1) p := by
    let r : ℝ := gamblerOddsRatio p
    have hr : p * r = 1 - p := by
      dsimp [r, gamblerOddsRatio]
      field_simp [hp] <;> ring
    have hsum : p + p * r = 1 := by linarith [hr]
    have hle : 1 ≤ i := hlo
    have hprev : r ^ i = r ^ (i - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hle]
      rw [pow_succ]
    have hnext : r ^ (i + 1) = r ^ i * r := pow_succ r i
    have hkey :
        1 - r ^ i =
          p * (1 - r ^ (i + 1)) + (1 - p) * (1 - r ^ (i - 1)) := by
      calc
        1 - r ^ i = (p + p * r) * (1 - r ^ i) := by rw [hsum]; ring
        _ = p * (1 - r ^ (i + 1)) + (1 - p) * (1 - r ^ (i - 1)) := by
          rw [hnext, hprev, ← hr] <;> ring
    change (1 - r ^ i) / (1 - r ^ N) =
      p * ((1 - r ^ (i + 1)) / (1 - r ^ N)) +
        (1 - p) * ((1 - r ^ (i - 1)) / (1 - r ^ N))
    rw [hkey] <;> ring
  have hN : 0 < N := lt_trans hlo hhi
  have hp_nonneg : 0 ≤ p := le_of_lt hp0
  exact ⟨hf, hb,
    gamblerFiniteSuccess_nonneg N n i p hp_nonneg hp1,
    gamblerFiniteRuin_nonneg N n i p hp_nonneg hp1,
    gamblerFiniteSuccessRuin_le_one N n i p hp_nonneg hp1 hN⟩
