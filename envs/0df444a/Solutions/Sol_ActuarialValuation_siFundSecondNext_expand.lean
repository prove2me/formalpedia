-- Prove2me | solution 1 for ActuarialValuation.siFundSecondNext_expand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:48.777994+00:00
-- url     : https://prove2.me/submissions/2f56c39b-3496-4fee-bd41-2524eb169597

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundSecondNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v m c q : ℝ) : siFundSecondNext v m c q=(v+2*c*m+c^2)*q := by
  rfl
