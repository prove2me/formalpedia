-- Prove2me | solution 1 for ActuarialValuation.pen9WithdrawalDeferredPV_zero_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:27.43655+00:00
-- url     : https://prove2.me/submissions/fec59c4e-c619-4a30-84db-63aba9dfc461

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9WithdrawalDeferredPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w b disc ann : ℝ) : pen9WithdrawalDeferredPV w b 0 disc ann = 0 := by
  simp [pen9WithdrawalDeferredPV]
