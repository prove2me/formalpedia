-- Prove2me | solution 1 for ActuarialValuation.cm1LastSurvivorIndicator_symm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:29.699028+00:00
-- url     : https://prove2.me/submissions/aabbd3bd-c513-47c0-9c2c-d6458aa9cc6e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LastSurvivorIndicator
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pX pY both : ℕ → ℝ) (t : ℕ) : cm1LastSurvivorIndicator pX pY both t = cm1LastSurvivorIndicator pY pX both t := by
  unfold cm1LastSurvivorIndicator
  ring
