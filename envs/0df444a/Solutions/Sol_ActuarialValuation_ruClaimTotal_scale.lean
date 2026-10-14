-- Prove2me | solution 1 for ActuarialValuation.ruClaimTotal_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:21:33.968789+00:00
-- url     : https://prove2.me/submissions/9b47e33d-d0e9-4545-9a7e-7b89d43ca54a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ruClaimTotal (fun k => r*x k) n = r*ruClaimTotal x n := by
  unfold ruClaimTotal
  calc
    (∑ k ∈ Finset.range n, r * x k) =
      (∑ k ∈ Finset.range n, x k * r) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = (∑ k ∈ Finset.range n, x k) * r := by
        rw [Finset.sum_mul]
    _ = r * (∑ k ∈ Finset.range n, x k) := by ring
