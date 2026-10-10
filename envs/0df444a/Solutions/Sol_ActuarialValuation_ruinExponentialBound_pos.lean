-- Prove2me | solution 1 for ActuarialValuation.ruinExponentialBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:42:05.973255+00:00
-- url     : https://prove2.me/submissions/75152132-dde8-4c27-b6a6-52858c24cc3d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R : ℝ) (u : ℤ) :
  0 < ruinExponentialBound R u := by
  exact Real.exp_pos _
