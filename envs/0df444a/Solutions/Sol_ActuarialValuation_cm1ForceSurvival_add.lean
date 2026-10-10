-- Prove2me | solution 1 for ActuarialValuation.cm1ForceSurvival_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:31:46.096474+00:00
-- url     : https://prove2.me/submissions/8782491d-38a0-45fe-af5c-067e91e9ab8e

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ s t : ℝ) : cm1ForceSurvival μ (s+t) = cm1ForceSurvival μ s * cm1ForceSurvival μ t := by
  change Real.exp (-μ * (s + t)) = Real.exp (-μ * s) * Real.exp (-μ * t)
  rw [mul_add, Real.exp_add]
