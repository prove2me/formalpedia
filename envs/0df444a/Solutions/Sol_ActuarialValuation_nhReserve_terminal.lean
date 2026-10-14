-- Prove2me | solution 1 for ActuarialValuation.nhReserve_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:36:31.982918+00:00
-- url     : https://prove2.me/submissions/1cc818fa-8977-4513-b561-af4e93e3c43a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p δ B1 B2 M T : ℝ) : nhReserve a b p δ B1 B2 M T T=M := by
  simp [nhReserve,nhEndowment,nhDeathPV,nhSurvival]
