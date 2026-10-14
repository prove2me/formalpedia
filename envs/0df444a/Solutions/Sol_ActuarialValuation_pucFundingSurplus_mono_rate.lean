-- Prove2me | solution 1 for ActuarialValuation.pucFundingSurplus_mono_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:57.17862+00:00
-- url     : https://prove2.me/submissions/6e0fef52-0c17-478e-8546-ccc3efdd9a3b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a al base c1 c2 : ℝ) (hb : 0 ≤ base) (h : c1 ≤ c2) : pucFundingSurplus a c1 base al ≤ pucFundingSurplus a c2 base al := by
  unfold pucFundingSurplus
  exact sub_le_sub_right
    (add_le_add_right (mul_le_mul_of_nonneg_right h hb) a) al
