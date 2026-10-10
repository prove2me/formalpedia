-- Prove2me | solution 1 for ActuarialValuation.cm1ReserveYearProfit_zero_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:38.759059+00:00
-- url     : https://prove2.me/submissions/9e1f882e-1e12-4c7b-9f4c-892c39608f3a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g : ℕ → ℝ) (t : ℕ) : cm1ReserveYearProfit c s g (fun _ => 0) t = c t := by
  simp [cm1ReserveYearProfit]
