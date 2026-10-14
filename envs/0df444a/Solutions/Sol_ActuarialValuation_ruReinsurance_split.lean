-- Prove2me | solution 1 for ActuarialValuation.ruReinsurance_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:26:43.525423+00:00
-- url     : https://prove2.me/submissions/be6645b3-78c0-4ea6-a321-9a4b50b46584

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruRetained
import Definitions.Def_actuarial_ruStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℝ) :
    ruRetained x d + ruStopLoss x d = x := by
  unfold ruRetained ruStopLoss
  rcases le_total x d with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h)]
    ring
