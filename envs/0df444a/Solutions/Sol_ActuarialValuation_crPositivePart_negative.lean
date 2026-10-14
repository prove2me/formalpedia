-- Prove2me | solution 1 for ActuarialValuation.crPositivePart_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:03.029616+00:00
-- url     : https://prove2.me/submissions/4e79e690-3080-4cf0-bc99-0b2c206afcf0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crPositivePart

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℝ) (h : x≤0) : crPositivePart x=0 := by
  unfold crPositivePart
  exact max_eq_right h
