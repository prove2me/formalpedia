-- Prove2me | solution 1 for ActuarialValuation.tailScaledExcess_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:19:18.49353+00:00
-- url     : https://prove2.me/submissions/89ea9dde-6963-4c9c-a76e-94fcd55af77f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailScaledExcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (excess frac : ℝ) (he : 0 ≤ excess) (hf : 0 < frac) :
    0 ≤ tailScaledExcess excess frac := by
  first
  | (simp only [tailScaledExcess]; positivity)
  | (unfold tailScaledExcess; positivity)
  | (unfold tailScaledExcess; exact div_nonneg he hf.le)
  | (simp [tailScaledExcess])
