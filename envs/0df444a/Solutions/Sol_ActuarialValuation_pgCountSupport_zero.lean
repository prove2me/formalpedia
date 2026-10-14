-- Prove2me | solution 1 for ActuarialValuation.pgCountSupport_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:16:41.732917+00:00
-- url     : https://prove2.me/submissions/53ead4e4-ca58-4e3e-b91f-10aed3319908

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountSupport
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (h : pgCountSupport p 0) (n : ℕ) (hn : n≠0) : p n=0 := by
  exact h n (Nat.pos_of_ne_zero hn)
