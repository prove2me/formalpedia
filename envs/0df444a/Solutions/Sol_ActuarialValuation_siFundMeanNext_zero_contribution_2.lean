-- Prove2me | solution 2 for ActuarialValuation.siFundMeanNext_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.701886+00:00
-- url     : https://prove2.me/submissions/c0e3161a-0506-48fb-a2b6-779a1eb983e1

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundMeanNext

open ActuarialValuation

theorem solution (priorMean meanGross : ℝ) : siFundMeanNext priorMean 0 meanGross=priorMean*meanGross := by simp [siFundMeanNext]

