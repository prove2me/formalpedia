-- Prove2me | solution 1 for ActuarialValuation.pen9RequiredDCRate_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:13:13.020214+00:00
-- url     : https://prove2.me/submissions/8bfc5f39-7cbf-4a98-b26e-9d5aa517e99f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredDCRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (capital factor rate : ℝ) (hf : factor ≠ 0) (h : rate*factor=capital) : rate = pen9RequiredDCRate capital factor := by
  change rate = capital / factor
  exact (eq_div_iff hf).mpr h
