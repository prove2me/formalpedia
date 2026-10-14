-- Prove2me | solution 1 for ActuarialValuation.irACPCReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:56:26.325978+00:00
-- url     : https://prove2.me/submissions/15db59ef-724d-4e93-84f4-97538cb3b420

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irACPCUltimate
import Definitions.Def_actuarial_irACPCReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (count avg paid : ℝ) : irACPCReserve count avg paid+paid=irACPCUltimate count avg := by
  unfold irACPCReserve irACPCUltimate
  ring
