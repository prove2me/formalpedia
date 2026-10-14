-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregatePGF_compose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:55:33.742991+00:00
-- url     : https://prove2.me/submissions/429a9e0d-e051-4125-91c9-e473b1c2ad86

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxBernAggregatePGF
import Definitions.Def_actuarial_cxBernCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 : ℝ) (f : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxBernAggregatePGF p0 p1 f n z = cxBernCountPGF p0 p1 (cxPGF f n z) := by
  rfl
