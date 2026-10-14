-- Prove2me | solution 1 for ActuarialValuation.cxObservedEvents_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:16.504979+00:00
-- url     : https://prove2.me/submissions/367128dc-b152-4963-a067-90c3d592bf5c

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
    Disjoint (cxObservedEvents fail censored) censored := by
  apply Finset.disjoint_left.mpr
  intro i hi hc
  unfold cxObservedEvents at hi
  exact (Finset.mem_sdiff.mp hi).2 hc
