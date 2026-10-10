-- Prove2me | solution 1 for ActuarialValuation.cm1EffectiveDiscount_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:26.695562+00:00
-- url     : https://prove2.me/submissions/0d74b9e6-a2c7-4fe4-a315-70ec9c63cb1e

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1EffectiveDiscount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (hi : -1 < i) :
    (1+i) * cm1EffectiveDiscount i = i := by
  have hn : 1 + i ≠ 0 := by linarith
  change (1+i) * (i / (1+i)) = i
  field_simp [hn]
