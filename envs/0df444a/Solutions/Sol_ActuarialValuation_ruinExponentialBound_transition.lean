-- Prove2me | solution 1 for ActuarialValuation.ruinExponentialBound_transition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:32.863979+00:00
-- url     : https://prove2.me/submissions/9f66bc65-970e-4e4c-a5ce-62d67d1cf1c5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (R : ℝ) (u : ℤ) (c k : ℕ) :
  ruinExponentialBound R (ruinNextSurplus u c k) =
    ruinExponentialBound R u *
      Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
  simp only [ruinExponentialBound, ruinNextSurplus]
  push_cast
  rw [← Real.exp_add]
  congr 1
  ring
