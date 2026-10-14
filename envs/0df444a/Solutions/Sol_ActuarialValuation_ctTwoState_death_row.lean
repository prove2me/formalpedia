-- Prove2me | solution 1 for ActuarialValuation.ctTwoState_death_row
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:43.030658+00:00
-- url     : https://prove2.me/submissions/f9dd60f3-c2fb-4fbb-af1f-a2162a439609

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu t : ℝ) : ctTwoState mu t 1 0=0 ∧ ctTwoState mu t 1 1=1 := by
  constructor <;> simp [ctTwoState]
