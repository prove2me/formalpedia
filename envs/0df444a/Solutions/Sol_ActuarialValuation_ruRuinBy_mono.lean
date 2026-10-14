-- Prove2me | solution 1 for ActuarialValuation.ruRuinBy_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:25:34.5232+00:00
-- url     : https://prove2.me/submissions/2fbedb23-0b6e-4ff4-ae4a-6c5876659069

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n m : ℕ)
    (h : n ≤ m) (hr : ruRuinBy u c x n) :
    ruRuinBy u c x m := by
  rcases hr with ⟨k, hk, hru⟩
  exact ⟨k, le_trans hk h, hru⟩
