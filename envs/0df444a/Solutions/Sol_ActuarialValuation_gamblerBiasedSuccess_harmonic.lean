-- Prove2me | solution 1 for ActuarialValuation.gamblerBiasedSuccess_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:54:31.861271+00:00
-- url     : https://prove2.me/submissions/62e44012-9a4c-4f57-a6e3-700b88d1dbec

import Mathlib.Tactic
import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerOddsRatio
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N i : ℕ) (p : ℝ)
    (hlo : 0 < i) (hhi : i < N) (hp : p ≠ 0)
    (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
    gamblerBiasedSuccess N i p =
      p * gamblerBiasedSuccess N (i + 1) p +
        (1 - p) * gamblerBiasedSuccess N (i - 1) p := by
  let r : ℝ := gamblerOddsRatio p
  have hr : p * r = 1 - p := by
    dsimp [r, gamblerOddsRatio]
    field_simp [hp]
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
        rw [hnext, hprev, ← hr]
        ring
  change (1 - r ^ i) / (1 - r ^ N) =
    p * ((1 - r ^ (i + 1)) / (1 - r ^ N)) +
      (1 - p) * ((1 - r ^ (i - 1)) / (1 - r ^ N))
  rw [hkey]
  ring

