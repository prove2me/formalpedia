-- Prove2me | solution 1 for ActuarialValuation.cm1LastSurvivorIndicator_ge_y
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:16.303361+00:00
-- url     : https://prove2.me/submissions/6835a8ad-1cb1-4979-9f05-94f580af5d3f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LastSurvivorIndicator
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pX pY both : ℕ → ℝ) (t : ℕ) (h : both t ≤ pX t) : pY t ≤ cm1LastSurvivorIndicator pX pY both t := by
  unfold cm1LastSurvivorIndicator
  linarith
