-- Prove2me | solution 1 for ActuarialValuation.ruStopLoss_above
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:38:31.221001+00:00
-- url     : https://prove2.me/submissions/b8f9fb63-65e7-40fd-bd24-f3ff72d17411

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruStopLoss
open ActuarialValuation

theorem solution(x d : ℝ) (h : d ≤ x) : ruStopLoss x d = x-d := by
  unfold ruStopLoss
  exact max_eq_right (by linarith)
