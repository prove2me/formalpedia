-- Prove2me | solution 1 for ActuarialValuation.ruFirstRuin_at
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:25:37.458426+00:00
-- url     : https://prove2.me/submissions/598f38df-17d7-4254-9111-5fe123ce2c80

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruFirstRuin
import Definitions.Def_actuarial_ruRuinAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : ruFirstRuin u c x n) : ruRuinAt u c x n := by
  exact h.1
