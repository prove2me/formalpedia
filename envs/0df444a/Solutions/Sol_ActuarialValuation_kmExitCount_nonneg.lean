-- Prove2me | solution 1 for ActuarialValuation.kmExitCount_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:06:19.503254+00:00
-- url     : https://prove2.me/submissions/7991af8f-3c1b-40ec-a5df-790e464aba6a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount
open ActuarialValuation

theorem solution(d c : ℝ) (hd : 0 ≤ d) (hc : 0 ≤ c) : 0 ≤ kmExitCount d c := by
  unfold kmExitCount
  linarith
