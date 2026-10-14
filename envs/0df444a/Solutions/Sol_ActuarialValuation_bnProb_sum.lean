-- Prove2me | solution 1 for ActuarialValuation.bnProb_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:18.644191+00:00
-- url     : https://prove2.me/submissions/cfe65083-91ab-4b9b-b8a5-ecf1f2968107

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb
import Definitions.Def_actuarial_bnRiskNeutralDown

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R : ℝ) : bnRiskNeutralProb u d R + bnRiskNeutralDown u d R = 1 := by
  unfold bnRiskNeutralDown
  ring
