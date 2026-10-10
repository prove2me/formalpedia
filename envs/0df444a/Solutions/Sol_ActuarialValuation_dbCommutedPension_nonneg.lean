-- Prove2me | solution 1 for ActuarialValuation.dbCommutedPension_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:06.672021+00:00
-- url     : https://prove2.me/submissions/8081e142-b91e-47e1-8e3e-924392625fe4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutedPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g L f : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) (hL : 0 ≤ L) (hcap : L ≤ f * g) :
  0 ≤ dbCommutedPension g L f := by
  unfold dbCommutedPension
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hf).2
  simpa [mul_comm] using hcap
