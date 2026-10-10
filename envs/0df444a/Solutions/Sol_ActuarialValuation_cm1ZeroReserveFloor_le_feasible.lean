-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveFloor_le_feasible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:34.907989+00:00
-- url     : https://prove2.me/submissions/6246e34c-6d61-4c33-9f11-f1db3db75a83

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g next R : ℝ) (hg : 0 < g) (hR : 0 ≤ R) (hprof : 0 ≤ c+g*R-s*next) : cm1ZeroReserveFloor c s g next ≤ R := by
  unfold cm1ZeroReserveFloor
  apply max_le hR
  apply (div_le_iff₀ hg).2
  nlinarith [hprof]
