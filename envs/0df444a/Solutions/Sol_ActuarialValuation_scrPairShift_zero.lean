-- Prove2me | solution 1 for ActuarialValuation.scrPairShift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:16.134012+00:00
-- url     : https://prove2.me/submissions/6cb0e8a4-7b90-4bbe-bffd-d6281e4d3375

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrPairShift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) : scrPairShift rho a b 0 = scrPairSquared rho a b := by
  simp [scrPairShift]
