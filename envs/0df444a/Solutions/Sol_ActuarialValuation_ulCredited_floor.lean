-- Prove2me | solution 1 for ActuarialValuation.ulCredited_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:00.457659+00:00
-- url     : https://prove2.me/submissions/9549bf38-1f0d-42bf-a573-f4b792809ac9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCreditedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (market participation floor cap : ℝ) : floor≤ulCreditedRate market participation floor cap := by
  change floor ≤ max floor (min cap (participation * market))
  exact le_max_left _ _
