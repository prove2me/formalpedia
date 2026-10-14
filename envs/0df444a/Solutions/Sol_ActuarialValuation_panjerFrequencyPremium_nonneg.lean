-- Prove2me | solution 1 for ActuarialValuation.panjerFrequencyPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:17.25299+00:00
-- url     : https://prove2.me/submissions/ebdd00a8-6c53-4a63-8dbc-41ebd95bc945

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerFrequencyPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda mean : ℝ) (hl : 0 ≤ lambda) (hm : 0 ≤ mean) : 0 ≤ panjerFrequencyPremium lambda mean := by
  unfold panjerFrequencyPremium
  exact mul_nonneg hl hm
