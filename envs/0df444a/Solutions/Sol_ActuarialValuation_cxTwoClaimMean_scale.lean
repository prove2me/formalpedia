-- Prove2me | solution 1 for ActuarialValuation.cxTwoClaimMean_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:55.648983+00:00
-- url     : https://prove2.me/submissions/6e7511db-e4b0-4ad5-b45d-13dd95649aa6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMean
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mean p1 p2 c : ℝ) : cxTwoClaimMean (c*mean) p1 p2 = c*cxTwoClaimMean mean p1 p2 := by
  unfold cxTwoClaimMean
  ring
