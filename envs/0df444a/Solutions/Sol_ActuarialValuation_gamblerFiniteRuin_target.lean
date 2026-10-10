-- Prove2me | solution 1 for ActuarialValuation.gamblerFiniteRuin_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:34.197995+00:00
-- url     : https://prove2.me/submissions/30e4a653-1ce1-4baf-83df-96d633195a3c

import Definitions.Def_actuarial_gamblerFiniteRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N n : ℕ) (p : ℝ) (hN : 0 < N) :
    gamblerFiniteRuin N p n N = 0 := by
  cases n <;> simp [gamblerFiniteRuin, Nat.ne_of_gt hN]
