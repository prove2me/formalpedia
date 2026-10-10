-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonExperienceWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:10.224966+00:00
-- url     : https://prove2.me/submissions/f4ab8b03-dbca-4c75-bb7d-1329ea90627a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (b e : ℝ) (hb : 0 < b) (he : 0 ≤ e) :
  0 ≤ gammaPoissonExperienceWeight b e := by
  change 0 ≤ e / (b + e)
  exact div_nonneg he (le_of_lt (add_pos_of_pos_of_nonneg hb he))
