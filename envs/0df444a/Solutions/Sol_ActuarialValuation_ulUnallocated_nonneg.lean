-- Prove2me | solution 1 for ActuarialValuation.ulUnallocated_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:00.588758+00:00
-- url     : https://prove2.me/submissions/000339c2-cd8f-4a50-8bd2-ebe754f4d0fc

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulUnallocated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (premium rate : ℝ) (hp : 0≤premium) (hr0 : 0≤rate) (hr1 : rate≤1) : 0≤ulUnallocated premium rate := by
  have h : 0 ≤ premium * (1-rate) :=
    mul_nonneg hp (sub_nonneg.mpr hr1)
  unfold ulUnallocated ulPremiumAlloc
  nlinarith
