-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteedRisk_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:08:25.214002+00:00
-- url     : https://prove2.me/submissions/4934ed40-5760-48da-ad2e-543a37d194f4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk
open ActuarialValuation

theorem solution(account floor : ℝ) : 0≤ulGuaranteedNetRisk account floor := by
  unfold ulGuaranteedNetRisk
  exact le_max_right _ _
