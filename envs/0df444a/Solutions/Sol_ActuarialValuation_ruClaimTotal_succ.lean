-- Prove2me | solution 1 for ActuarialValuation.ruClaimTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:13:18.684084+00:00
-- url     : https://prove2.me/submissions/2eb92d4f-e081-4743-bb9d-ad78f330fd86

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℝ) (n : ℕ) :
    ruClaimTotal x (n+1) = ruClaimTotal x n + x n := by
  simp [ruClaimTotal, Finset.sum_range_succ]
