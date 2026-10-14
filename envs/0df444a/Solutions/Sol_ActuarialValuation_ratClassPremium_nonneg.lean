-- Prove2me | solution 1 for ActuarialValuation.ratClassPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:22:50.320006+00:00
-- url     : https://prove2.me/submissions/df47d173-9aec-40fc-91b1-76bf9224f561

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e base rel : ℝ) (he : 0 ≤ e) (hb : 0 ≤ base)
    (hr : 0 ≤ rel) : 0 ≤ ratClassPremium e base rel := by
  unfold ratClassPremium
  exact mul_nonneg (mul_nonneg he hb) hr
