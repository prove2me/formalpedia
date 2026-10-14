-- Prove2me | solution 1 for ActuarialValuation.irNominalOutstanding_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:06:20.046616+00:00
-- url     : https://prove2.me/submissions/dd164236-11ac-43a2-b040-a6d41b3ba563

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irNominalOutstanding

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (real a b : ℝ) (hb : b≠0) : irNominalOutstanding real (a*b) b=real*a := by
  unfold irNominalOutstanding irReinflate
  field_simp [hb]
