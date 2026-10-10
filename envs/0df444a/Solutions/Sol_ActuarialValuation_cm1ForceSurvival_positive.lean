-- Prove2me | solution 1 for ActuarialValuation.cm1ForceSurvival_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:31:58.410314+00:00
-- url     : https://prove2.me/submissions/60814eef-ef3a-4470-9c22-d066297833b0

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ t : ℝ) : 0 < cm1ForceSurvival μ t := by
  change 0 < Real.exp (-μ*t)
  exact Real.exp_pos _
