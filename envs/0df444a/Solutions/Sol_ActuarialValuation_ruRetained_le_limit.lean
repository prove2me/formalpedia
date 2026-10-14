-- Prove2me | solution 1 for ActuarialValuation.ruRetained_le_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:23:43.949243+00:00
-- url     : https://prove2.me/submissions/d1be1539-a4d1-4fc8-ae82-cf24b2c80179

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRetained

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℝ) : ruRetained x d ≤ d := by
  unfold ruRetained
  exact min_le_right x d
