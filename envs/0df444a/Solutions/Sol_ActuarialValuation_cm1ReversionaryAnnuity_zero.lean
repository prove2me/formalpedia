-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:47.197749+00:00
-- url     : https://prove2.me/submissions/be63a755-d3e5-4022-88dc-1f612e51e052

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pY both : ℕ → ℝ) : cm1ReversionaryAnnuity discount pY both 0 = 0 := by
  simp [cm1ReversionaryAnnuity]
