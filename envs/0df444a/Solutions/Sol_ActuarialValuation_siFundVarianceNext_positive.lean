-- Prove2me | solution 1 for ActuarialValuation.siFundVarianceNext_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:04:13.822003+00:00
-- url     : https://prove2.me/submissions/c5f931e9-05be-4309-a27b-d78a30a39fb9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundVarianceNext

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v m c gross q : ℝ) (hv : m^2≤v) (hq : gross^2≤q) (hm : 0≤gross) : 0≤siFundVarianceNext v m c gross q := by
  have hq_nonneg : 0 ≤ q := le_trans (sq_nonneg gross) hq
  have hv_nonneg : 0 ≤ v-m^2 := sub_nonneg.mpr hv
  have hq_delta : 0 ≤ q-gross^2 := sub_nonneg.mpr hq
  calc
    siFundVarianceNext v m c gross q =
        (v-m^2)*q + (m+c)^2*(q-gross^2) := by
          unfold siFundVarianceNext siFundSecondNext siFundMeanNext
          ring
    _ ≥ 0 := add_nonneg (mul_nonneg hv_nonneg hq_nonneg)
      (mul_nonneg (sq_nonneg (m+c)) hq_delta)
