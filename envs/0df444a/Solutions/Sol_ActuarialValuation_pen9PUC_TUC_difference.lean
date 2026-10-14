-- Prove2me | solution 1 for ActuarialValuation.pen9PUC_TUC_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:18:43.87501+00:00
-- url     : https://prove2.me/submissions/a0604da8-2575-49a1-b6cb-f0c00a3d99cc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9TUC

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a current projected f : ℝ) (n : ℕ) : pen9PUC a projected f n - pen9TUC a current f n = a*(n:ℝ)*(projected-current)*f := by
  unfold pen9PUC pen9TUC
  ring
