-- Prove2me | solution 1 for ActuarialValuation.ruTwoScenarioRuin_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:29:51.774954+00:00
-- url     : https://prove2.me/submissions/e046ec55-e17e-4b75-8ca4-3232277fc103

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ruTwoScenarioRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p+q=1) (a b : Bool) :
    ruTwoScenarioRuin p q a b ≤ 1 := by
  cases a <;> cases b <;>
    simp [ruTwoScenarioRuin] <;> linarith
