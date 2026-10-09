-- Prove2me | solution 1 for ActuarialValuation.cededExcessLoss_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:43:28.961177+00:00
-- url     : https://prove2.me/submissions/c57be3e9-854b-45d1-9382-341c93282ce6

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss

open ActuarialValuation

theorem solution (z a : ℝ) : 0 ≤ cededExcessLoss z a := by
  unfold cededExcessLoss
  have := min_le_left z a
  linarith
