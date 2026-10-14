-- Prove2me | solution 1 for ActuarialValuation.ruDeficit_at_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:00:43.41257+00:00
-- url     : https://prove2.me/submissions/bad33407-328a-47dd-8679-e1a584267896

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinDeficit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (capital : ℝ) (h : capital < 0) :
    ruRuinDeficit capital = -capital := by
  first
  | (unfold ruRuinDeficit; rw [max_eq_left (le_of_lt (neg_pos.mpr h))])
  | (unfold ruRuinDeficit; simp)
  | (simp [ruRuinDeficit])
