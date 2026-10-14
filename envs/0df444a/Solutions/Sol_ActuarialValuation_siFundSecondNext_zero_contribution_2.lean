-- Prove2me | solution 2 for ActuarialValuation.siFundSecondNext_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.439602+00:00
-- url     : https://prove2.me/submissions/604f0d68-f961-4b81-8fe3-831f5b5b500e

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundSecondNext

open ActuarialValuation

theorem solution (priorSecond priorMean secondGross : ℝ) : siFundSecondNext priorSecond priorMean 0 secondGross=priorSecond*secondGross := by simp [siFundSecondNext]

