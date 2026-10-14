-- Prove2me | solution 1 for ActuarialValuation.pen9RequiredContribution_no_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:16:16.490367+00:00
-- url     : https://prove2.me/submissions/b541e0d2-c6c3-4916-826b-61dae60dfd06

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredContribution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (reserve exitPV : ℝ) : pen9RequiredContribution reserve exitPV 0 0 = exitPV-reserve := by
  simp [pen9RequiredContribution]
