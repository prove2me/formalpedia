-- Prove2me | solution 1 for ActuarialValuation.mackOneStepMSE_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:11.788995+00:00
-- url     : https://prove2.me/submissions/8d04cf58-3efb-4adf-8515-e85c8cbd91d8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackOneStepMSE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p e : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) : 0 ≤ mackOneStepMSE p e := by
  unfold mackOneStepMSE
  exact add_nonneg hp he
