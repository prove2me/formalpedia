-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_first_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:33:58.872433+00:00
-- url     : https://prove2.me/submissions/352ce1f5-853d-479e-8a24-96c94b4a8117

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerAdjustment
import Definitions.Def_actuarial_cxPanjerFirstRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b f0 f1 g0 g1 : ℝ) (h : cxPanjerAdjustment a f0 ≠ 0) (heq : g1*cxPanjerAdjustment a f0 = cxPanjerFirstRHS a b f1 g0) : g1 = cxPanjerFirstRHS a b f1 g0 / cxPanjerAdjustment a f0 := by
  exact (eq_div_iff h).2 heq
