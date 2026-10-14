-- Prove2me | solution 1 for ActuarialValuation.siFundMeanNext_add_contribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:30.015767+00:00
-- url     : https://prove2.me/submissions/b04fe28d-88c2-46e0-ace3-57d7446da2f5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundMeanNext

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (priorMean a b gross : ℝ) : siFundMeanNext priorMean (a+b) gross=siFundMeanNext priorMean a gross+b*gross := by
  unfold siFundMeanNext
  ring
