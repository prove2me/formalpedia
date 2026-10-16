-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_integer_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T05:59:47.295977+00:00
-- url     : https://prove2.me/submissions/94faa132-fe65-412e-9602-cff9c674df95

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bcSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution (h t : ℕ) (p : ℕ → ℝ) :
    ActuarialAnnuitiesContinuous.bcSurvival h p (fun k => (k : ℝ)) (t : ℝ) =
      ActuarialAnnuities.bSurvival h p t := by
  simp [ActuarialAnnuitiesContinuous.bcSurvival,
        ActuarialAnnuities.bSurvival,
        ActuarialAnnuitiesContinuous.bcAlive,
        ActuarialAnnuities.bAlive]
