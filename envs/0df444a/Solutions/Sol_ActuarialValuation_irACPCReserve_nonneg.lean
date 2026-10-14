-- Prove2me | solution 1 for ActuarialValuation.irACPCReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:04:21.455978+00:00
-- url     : https://prove2.me/submissions/be6c8961-58c6-4ec4-9ea8-b955c77293b1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irACPCUltimate
import Definitions.Def_actuarial_irACPCReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (count avg paid : ℝ) (h : paid≤irACPCUltimate count avg) : 0≤irACPCReserve count avg paid := by
  unfold irACPCReserve
  exact sub_nonneg.mpr h
