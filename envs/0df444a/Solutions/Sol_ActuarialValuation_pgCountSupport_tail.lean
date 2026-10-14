-- Prove2me | solution 1 for ActuarialValuation.pgCountSupport_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:49:34.960551+00:00
-- url     : https://prove2.me/submissions/bd438073-a3a5-4792-92e3-bc4d5cc37d7f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountSupport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (m n : ℕ) (h : pgCountSupport p m) (hm : m<n) : p n=0 := by
  exact h n hm
