-- Prove2me | solution 1 for ActuarialValuation.pfEntryLiability_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:48.216771+00:00
-- url     : https://prove2.me/submissions/4f0b5ad6-6603-4fe1-aa30-38f35a66f331

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryLiability
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit pay rate : ℝ) : pfEntryLiability benefit pay rate+rate*pay=benefit := by
  unfold pfEntryLiability
  ring
