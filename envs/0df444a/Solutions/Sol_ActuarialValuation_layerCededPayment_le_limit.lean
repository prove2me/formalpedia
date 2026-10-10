-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_le_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:44:57.60393+00:00
-- url     : https://prove2.me/submissions/50c0cc91-b20a-4557-9a41-eef6a4e36c05

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ) :
  layerCededPayment x d L ≤ L := by
  exact min_le_right _ _
