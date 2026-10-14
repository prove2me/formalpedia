-- Prove2me | solution 1 for ActuarialValuation.frForce_product
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:23:12.02368+00:00
-- url     : https://prove2.me/submissions/27b59ce8-1a36-4c47-867b-7bf643526d65

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival
open ActuarialValuation

theorem solution(mu s t : ℝ) : frForceSurvival mu (s+t) = frForceSurvival mu s * frForceSurvival mu t := by
  unfold frForceSurvival
  rw [<- Real.exp_add]
  ring_nf
