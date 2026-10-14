-- Prove2me | solution 1 for ActuarialValuation.cxTwoClaimMoment_two_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:35:13.271744+00:00
-- url     : https://prove2.me/submissions/4bcbceab-80bb-4aae-925e-7304e6cbb6f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMoment
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu m2 p1 p2 : ℝ) : cxTwoClaimMoment mu m2 p1 p2 = (p1+2*p2)*m2+2*p2*mu^2 := by
  unfold cxTwoClaimMoment
  ring
