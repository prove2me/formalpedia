-- Prove2me | solution 1 for ActuarialValuation.ulCredited_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:13.558127+00:00
-- url     : https://prove2.me/submissions/a0c33c7b-3e79-4069-aa2c-a35d1a15d3f2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCreditedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (market participation floor cap : ℝ) (h : floor≤cap) : ulCreditedRate market participation floor cap ≤ cap := by
  change max floor (min cap (participation * market)) ≤ cap
  exact max_le h (min_le_left _ _)
