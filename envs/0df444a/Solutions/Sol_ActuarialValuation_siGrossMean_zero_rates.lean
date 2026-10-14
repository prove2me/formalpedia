-- Prove2me | solution 1 for ActuarialValuation.siGrossMean_zero_rates
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:26:54.389987+00:00
-- url     : https://prove2.me/submissions/7b9ad9af-3925-4fab-bdb4-d75b283b9a7c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossMean
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) (hp : (∑ j : Fin m, p j)=1) : siGrossMean p (fun _ => 0)=1 := by
  unfold siGrossMean siMean siGrowth
  simpa using hp
