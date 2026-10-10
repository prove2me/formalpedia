-- Prove2me | solution 1 for ActuarialValuation.poissonCountMass_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:32:06.926382+00:00
-- url     : https://prove2.me/submissions/960d071a-8b49-43ab-8caf-4daf5f2cf45b

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_poissonCountMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * poissonCountMass rate (n + 1) =
      rate * poissonCountMass rate n := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  dsimp [poissonCountMass]
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
