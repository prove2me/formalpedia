-- Prove2me | solution 1 for ActuarialValuation.pgPointMass_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:15:49.378042+00:00
-- url     : https://prove2.me/submissions/e2d92d8c-dc17-48c1-a149-a9400ca497f5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
open ActuarialValuation

theorem solution(k : ℕ) (hk : 0 < k) : pgPointMass k=0 := by
  unfold pgPointMass
  rw [if_neg (by omega)]
