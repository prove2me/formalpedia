-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryAnnuity_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:58.261085+00:00
-- url     : https://prove2.me/submissions/25a3ce02-3494-478e-b04c-27d6d0ce8d12

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ReversionaryIndicator
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pY both : ℕ → ℝ) (n : ℕ) : cm1ReversionaryAnnuity discount pY both (n+1) = cm1ReversionaryAnnuity discount pY both n + discount n * cm1ReversionaryIndicator pY both n := by
  simp [cm1ReversionaryAnnuity, Finset.sum_range_succ]
