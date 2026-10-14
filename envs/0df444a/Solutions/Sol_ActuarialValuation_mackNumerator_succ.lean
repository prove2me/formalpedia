-- Prove2me | solution 1 for ActuarialValuation.mackNumerator_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:33:24.357764+00:00
-- url     : https://prove2.me/submissions/795f13bc-0c56-434a-8f27-dae1d95365d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) : mackNumerator c (m+1) j = mackNumerator c m j + c m (j+1) := by
  simp [mackNumerator, Finset.sum_range_succ]
