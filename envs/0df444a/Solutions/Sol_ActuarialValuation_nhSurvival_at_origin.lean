-- Prove2me | solution 1 for ActuarialValuation.nhSurvival_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:47.060006+00:00
-- url     : https://prove2.me/submissions/8c873484-8ded-4d71-a3ea-ef7d8b51e350

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCumulative
import Definitions.Def_actuarial_nhSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b t : ℝ) : nhSurvival a b 0 t=Real.exp (-nhCumulative a b t) := by
  simp [nhSurvival,nhCumulative]
