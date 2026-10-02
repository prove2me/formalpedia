-- Prove2me | solution 1 for AppliedComb.GenFun.fallingP_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:41:04.388002+00:00
-- url     : https://prove2.me/submissions/1abce900-a59d-4b2b-855e-06a5eede730b

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

set_option autoImplicit false

open AppliedComb.GenFun in
theorem solution (p : ℝ) (k : ℕ) :
    fallingP p (k + 1) = fallingP p k * (p - k) := by
  induction k generalizing p with
  | zero => simp [fallingP]
  | succ n ih =>
    rw [fallingP, ih (p - 1), fallingP]
    push_cast
    ring
