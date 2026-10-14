-- Prove2me | solution 1 for ActuarialAnnuities.udd_monotone
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:09:40.530046+00:00
-- url     : https://prove2.me/submissions/54562878-5e01-449f-b19b-c39b4f22b4fe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDD
open ActuarialAnnuities

theorem solution(s0 s1 f g : ℝ) (hs : s1 ≤ s0) (hfg : f ≤ g) : bUDD s0 s1 g ≤ bUDD s0 s1 f := by
  unfold bUDD
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hfg)]
