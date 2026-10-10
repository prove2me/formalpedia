-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryIndicator_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:19.637377+00:00
-- url     : https://prove2.me/submissions/4a1ce537-3e62-4f94-b2fb-b3c917c637c8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ReversionaryIndicator
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pY both : ℕ → ℝ) (t : ℕ) : cm1ReversionaryIndicator pY both t + both t = pY t := by
  unfold cm1ReversionaryIndicator
  ring
