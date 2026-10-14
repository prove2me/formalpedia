-- Prove2me | solution 1 for ActuarialValuation.irDevelopmentFactor_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:01:24.444077+00:00
-- url     : https://prove2.me/submissions/059ccdc0-288a-4e59-9dcb-7466a251fad6

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDevelopmentFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (latest previous : ℝ) (h : previous≠0) : irDevelopmentFactor latest previous*previous=latest := by
  unfold irDevelopmentFactor
  field_simp [h]
