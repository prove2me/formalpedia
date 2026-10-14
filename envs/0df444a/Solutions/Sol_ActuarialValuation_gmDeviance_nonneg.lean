-- Prove2me | solution 1 for ActuarialValuation.gmDeviance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:46.407592+00:00
-- url     : https://prove2.me/submissions/b648018e-dc53-4e5c-9264-bed62b75dc1f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_gmPoissonDeviance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims expected : ℝ) (hc : 0 < claims)
    (he : 0 < expected) : 0 ≤ gmPoissonDeviance claims expected := by
  have hratio : 0 < expected / claims := div_pos he hc
  have hlog : Real.log (expected / claims) ≤ expected / claims - 1 :=
    Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt he) (ne_of_gt hc)] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hc.le
  have hid : claims * (expected / claims) = expected := by
    field_simp
  have hdiff : 0 ≤
      claims * Real.log claims - claims -
        (claims * Real.log expected - expected) := by
    nlinarith [hmul]
  unfold gmPoissonDeviance gmSaturatedLike gmPoissonLogLike
  nlinarith
