-- Prove2me | solution 1 for ActuarialValuation.pen9RequiredContribution_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:33.254704+00:00
-- url     : https://prove2.me/submissions/7381cbb8-d233-4ba6-ae25-5b51e8d2d5e0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredContribution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (reserve exitPV pActive next c : ℝ) (h : reserve+c = exitPV+pActive*next) : c = pen9RequiredContribution reserve exitPV pActive next := by
  unfold pen9RequiredContribution
  linarith
