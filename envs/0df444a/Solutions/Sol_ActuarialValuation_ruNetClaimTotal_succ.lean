-- Prove2me | solution 1 for ActuarialValuation.ruNetClaimTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:31:40.920817+00:00
-- url     : https://prove2.me/submissions/e6a9c1fa-04df-49b8-97a1-3aae7ca71ba0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruNetClaimTotal
import Definitions.Def_actuarial_ruNetClaim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    ruNetClaimTotal x c (n+1) =
      ruNetClaimTotal x c n + ruNetClaim (x n) c := by
  simp [ruNetClaimTotal, Finset.sum_range_succ]
