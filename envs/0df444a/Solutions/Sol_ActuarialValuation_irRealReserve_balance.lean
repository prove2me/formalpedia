-- Prove2me | solution 1 for ActuarialValuation.irRealReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:03:31.132688+00:00
-- url     : https://prove2.me/submissions/dc3d465a-c414-40ab-afc9-ea8dc6c62266

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irRealReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (ultimate paid : ℝ) : irRealReserve ultimate paid+paid=ultimate := by
  unfold irRealReserve
  ring
