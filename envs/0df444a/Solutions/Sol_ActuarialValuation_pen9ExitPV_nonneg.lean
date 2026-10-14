-- Prove2me | solution 1 for ActuarialValuation.pen9ExitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:20:37.209177+00:00
-- url     : https://prove2.me/submissions/72f928b9-476d-4927-87ea-636d19d07fca

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v w d i r bw bd bi br : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (hd : 0 ≤ d) (hi : 0 ≤ i) (hr : 0 ≤ r) (hbw : 0 ≤ bw) (hbd : 0 ≤ bd) (hbi : 0 ≤ bi) (hbr : 0 ≤ br) : 0 ≤ pen9ExitPV v w d i r bw bd bi br := by
  unfold pen9ExitPV
  apply mul_nonneg hv
  have h1 := mul_nonneg hw hbw
  have h2 := mul_nonneg hd hbd
  have h3 := mul_nonneg hi hbi
  have h4 := mul_nonneg hr hbr
  linarith
