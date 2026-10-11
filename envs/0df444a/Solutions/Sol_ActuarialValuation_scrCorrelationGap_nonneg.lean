-- Prove2me | solution 1 for ActuarialValuation.scrCorrelationGap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:16:28.253377+00:00
-- url     : https://prove2.me/submissions/fbe4f381-17d8-40c9-877d-cdfb3b960bbe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCorrelationGap
open ActuarialValuation

theorem solution(rho : ℝ) (hr : rho ≤ 1) : 0 ≤ scrCorrelationGap rho := by
  unfold scrCorrelationGap
  linarith
