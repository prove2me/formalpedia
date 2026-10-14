-- Prove2me | solution 1 for ActuarialValuation.ctAliveThiele_zero_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:02.215927+00:00
-- url     : https://prove2.me/submissions/d5c0ba6e-dbab-46a7-aff8-2f4c66294a3e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctInsuranceFlow
import Definitions.Def_actuarial_ctAliveThiele

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (delta mu b death : ℝ) : ctAliveThiele delta mu b death 0=-ctInsuranceFlow b mu death := by
  simp [ctAliveThiele]
