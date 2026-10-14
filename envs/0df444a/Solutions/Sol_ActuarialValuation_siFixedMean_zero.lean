-- Prove2me | solution 1 for ActuarialValuation.siFixedMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:26:56.493675+00:00
-- url     : https://prove2.me/submissions/817b87b8-f803-4779-b2c2-0e192ac0fe10

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedMean
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (h : (∑ j : Fin m, p j)=1) : siFixedMean p r 0=1 := by
  unfold siFixedMean siMean siFixedAccum
  simpa using h
