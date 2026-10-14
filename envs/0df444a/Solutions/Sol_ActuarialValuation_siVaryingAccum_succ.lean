-- Prove2me | solution 1 for ActuarialValuation.siVaryingAccum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:39.691984+00:00
-- url     : https://prove2.me/submissions/4ccbf1fd-116d-4167-af72-9847ecea7e8a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrowth
import Definitions.Def_actuarial_siVaryingAccum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ → ℝ) (n : ℕ) : siVaryingAccum r (n+1)=siVaryingAccum r n*siGrowth (r n) := by
  unfold siVaryingAccum
  simp only [Finset.prod_range_succ]
