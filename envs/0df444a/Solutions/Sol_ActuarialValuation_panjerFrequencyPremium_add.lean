-- Prove2me | solution 1 for ActuarialValuation.panjerFrequencyPremium_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:05.438675+00:00
-- url     : https://prove2.me/submissions/cc058005-351d-43a8-bf17-9c8084789bc3

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerFrequencyPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda m1 m2 : ℝ) : panjerFrequencyPremium lambda (m1+m2) = panjerFrequencyPremium lambda m1 + panjerFrequencyPremium lambda m2 := by
  unfold panjerFrequencyPremium
  ring
