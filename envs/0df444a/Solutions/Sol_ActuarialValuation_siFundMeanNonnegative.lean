-- Prove2me | solution 1 for ActuarialValuation.siFundMeanNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:31.918477+00:00
-- url     : https://prove2.me/submissions/180022f6-89cd-4246-bc73-e7b90b915908

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundMeanNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (m c gross : ℝ) (hm : 0≤m) (hc : 0≤c) (hg : 0≤gross) : 0≤siFundMeanNext m c gross := by
  unfold siFundMeanNext
  exact mul_nonneg (add_nonneg hm hc) hg
