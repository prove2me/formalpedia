-- Prove2me | solution 1 for ActuarialValuation.ratLossRatio_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:19:47.259972+00:00
-- url     : https://prove2.me/submissions/0d18151c-d6b2-4bd2-8020-947552f9a302

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratLossRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims premium : ℝ) (hp : premium ≠ 0) :
    ratLossRatio claims premium * premium = claims := by
  unfold ratLossRatio
  exact div_mul_cancel₀ claims hp
