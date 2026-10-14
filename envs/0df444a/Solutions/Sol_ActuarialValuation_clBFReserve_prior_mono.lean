-- Prove2me | solution 1 for ActuarialValuation.clBFReserve_prior_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:07:24.619184+00:00
-- url     : https://prove2.me/submissions/63ef2edb-edde-4867-a5b9-13e7a5e6f7c6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e1 e2 f : ℝ) (he : e1 ≤ e2) (hf : 1 ≤ f) : clBFReserve e1 f ≤ clBFReserve e2 f := by
  have hfpos : 0 < f := by linarith
  have hpaid : (1 : ℝ) / f ≤ 1 := by
    apply (div_le_iff₀ hfpos).2
    simpa using hf
  have hunpaid : 0 ≤ (1 : ℝ) - 1 / f := sub_nonneg.mpr hpaid
  change e1 * (1 - 1 / f) ≤ e2 * (1 - 1 / f)
  exact mul_le_mul_of_nonneg_right he hunpaid
