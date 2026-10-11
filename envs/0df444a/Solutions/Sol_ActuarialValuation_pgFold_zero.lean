-- Prove2me | solution 1 for ActuarialValuation.pgFold_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:23:19.720082+00:00
-- url     : https://prove2.me/submissions/aa09a355-8247-4638-8782-ef6762ef090c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (k : ℕ) : pgFold f 0 k = pgPointMass k := by
  rfl
