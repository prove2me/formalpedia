-- Prove2me | solution 1 for ActuarialValuation.ruClaimTotal_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:12:22.059912+00:00
-- url     : https://prove2.me/submissions/a1607a4f-207e-4497-a55e-30a3586029d6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x y : ℕ → ℝ) (n : ℕ) :
    ruClaimTotal (fun k => x k+y k) n = ruClaimTotal x n+ruClaimTotal y n := by
  unfold ruClaimTotal
  simp only [Finset.sum_add_distrib]
