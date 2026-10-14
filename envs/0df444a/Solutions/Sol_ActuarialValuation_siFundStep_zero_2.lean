-- Prove2me | solution 2 for ActuarialValuation.siFundStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:42.290971+00:00
-- url     : https://prove2.me/submissions/f0917d01-c7d0-407b-96d4-2fd82e2af33d

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep

open ActuarialValuation

theorem solution (fund contribution : ℝ) : siFundStep fund contribution 1=fund+contribution := by simp [siFundStep]

