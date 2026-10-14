-- Prove2me | solution 1 for ActuarialValuation.ulAllocated_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:04:49.339954+00:00
-- url     : https://prove2.me/submissions/400e1823-585c-4b5d-8a6a-b6db41d5dc67

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (prem : ℝ) : ulAllocatedPremium prem 0 = prem := by
  simp [ulAllocatedPremium]
