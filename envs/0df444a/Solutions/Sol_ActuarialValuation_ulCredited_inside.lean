-- Prove2me | solution 1 for ActuarialValuation.ulCredited_inside
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:25.576196+00:00
-- url     : https://prove2.me/submissions/ae0358c6-8b18-4d10-9742-a2bc33334ac8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCreditedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (market participation floor cap : ℝ) (h1 : floor≤participation*market) (h2 : participation*market≤cap) : ulCreditedRate market participation floor cap = participation*market := by
  change max floor (min cap (participation * market)) = participation * market
  rw [min_eq_right h2, max_eq_right h1]
