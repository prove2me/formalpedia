-- Prove2me | solution 1 for ActuarialValuation.ipCDF_successor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:10.383179+00:00
-- url     : https://prove2.me/submissions/e3fa05ad-c475-4f9e-830a-a18c9be6d72c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (k : ℕ) : ipCDF p f (k+1)=ipCDF p f k+ipCompound p f (k+1) := by
  unfold ipCDF
  simp only [Finset.sum_range_succ]
