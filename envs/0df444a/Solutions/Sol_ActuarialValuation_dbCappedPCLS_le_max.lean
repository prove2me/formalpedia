-- Prove2me | solution 1 for ActuarialValuation.dbCappedPCLS_le_max
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:39.461309+00:00
-- url     : https://prove2.me/submissions/aa2c2cee-3013-4f9c-9987-f78e0d824afd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCappedPCLS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f A : ℝ) :
  dbCappedPCLS g f A ≤ dbHMRCMaximumCash g f := by
  unfold dbCappedPCLS
  exact min_le_left _ _
