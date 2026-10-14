-- Prove2me | solution 1 for ActuarialValuation.cxObservedEvents_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:07.314368+00:00
-- url     : https://prove2.me/submissions/21f0cbc3-7342-4714-98c4-514b1e7ba349

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxObservedEvents

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (fail censored : Finset (Fin n)) :
    cxObservedEvents fail censored ⊆ fail := by
  intro i hi
  unfold cxObservedEvents at hi
  exact (Finset.mem_sdiff.mp hi).1
