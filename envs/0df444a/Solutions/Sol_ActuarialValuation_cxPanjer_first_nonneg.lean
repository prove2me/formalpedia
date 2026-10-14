-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_first_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:40:43.397612+00:00
-- url     : https://prove2.me/submissions/fce979ca-679d-4ff1-b40d-ce2c4d589d73

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerFirstRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b f1 g0 : ℝ) (hab : 0 ≤ a+b) (hf : 0 ≤ f1) (hg : 0 ≤ g0) : 0 ≤ cxPanjerFirstRHS a b f1 g0 := by
  simpa only [cxPanjerFirstRHS] using mul_nonneg (mul_nonneg hab hf) hg
