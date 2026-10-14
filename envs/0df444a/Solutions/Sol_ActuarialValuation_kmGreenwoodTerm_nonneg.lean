-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:07.191373+00:00
-- url     : https://prove2.me/submissions/486729d1-74a5-4d16-819f-d7f3931b41ae

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmGreenwoodTerm

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d r : ℝ) (hd : 0 ≤ d) (hr : d < r) : 0 ≤ kmGreenwoodTerm d r := by
  unfold kmGreenwoodTerm
  apply div_nonneg hd
  exact mul_nonneg (le_trans hd (le_of_lt hr)) (sub_nonneg.mpr (le_of_lt hr))
