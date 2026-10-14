-- Prove2me | solution 1 for ActuarialValuation.irIncrement_telescopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:44.358158+00:00
-- url     : https://prove2.me/submissions/23f9b128-5431-473b-82f7-ec1ea8bac7de

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irIncrement
import Definitions.Def_actuarial_irCumulative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (row : ℕ → ℝ) (n : ℕ) : irCumulative (irIncrement row) n=row n-row 0 := by
  induction n with
  | zero =>
      simp [irCumulative]
  | succ n ih =>
      have hs : irCumulative (irIncrement row) (n+1) =
          irCumulative (irIncrement row) n + irIncrement row n := by
        unfold irCumulative
        rw [Finset.sum_range_succ]
      rw [hs, ih]
      unfold irIncrement
      ring
