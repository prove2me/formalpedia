-- Prove2me | solution 1 for ActuarialValuation.ruDeficit_no_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:15:06.101612+00:00
-- url     : https://prove2.me/submissions/63b43a57-89ab-46c1-afbc-faf9f91a2cdd

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinDeficit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (capital : ℝ) (h : 0 ≤ capital) :
    ruRuinDeficit capital = 0 := by
  first
  | (unfold ruRuinDeficit; rw [max_eq_right (neg_nonpos.mpr h)])
  | (unfold ruRuinDeficit; simp)
  | (simp [ruRuinDeficit])
