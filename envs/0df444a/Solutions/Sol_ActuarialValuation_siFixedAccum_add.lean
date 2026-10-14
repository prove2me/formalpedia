-- Prove2me | solution 1 for ActuarialValuation.siFixedAccum_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:56:50.475985+00:00
-- url     : https://prove2.me/submissions/e228ecd1-58b7-4bbc-8588-32fbef298a8e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedAccum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (m n : ℕ) : siFixedAccum i (m+n)=siFixedAccum i m*siFixedAccum i n := by
  unfold siFixedAccum
  exact pow_add (siGrowth i) m n
