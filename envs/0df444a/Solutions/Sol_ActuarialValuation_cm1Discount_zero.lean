-- Prove2me | solution 1 for ActuarialValuation.cm1Discount_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:48.685068+00:00
-- url     : https://prove2.me/submissions/f5c3ce42-8663-4a1e-9735-ad92f613c201

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1Accum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1Discount i 0 = 1 := by
  simp [cm1Discount, cm1Accum]
