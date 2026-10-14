-- Prove2me | solution 1 for ActuarialValuation.panjerUpperTail_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:52.432275+00:00
-- url     : https://prove2.me/submissions/47d836df-93b5-47b1-8023-7845d666082b

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF
import Definitions.Def_actuarial_panjerUpperTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) : panjerAggregateCDF g n + panjerUpperTail g n = 1 := by
  unfold panjerUpperTail
  ring
