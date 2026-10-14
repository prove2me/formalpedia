-- Prove2me | solution 1 for ActuarialValuation.siFundVarianceNext_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:59.670052+00:00
-- url     : https://prove2.me/submissions/0ae1e412-748c-4706-82b1-fe414eab831e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundVarianceNext

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v m c gross secondGross : ℝ) (hv : v=m^2) (hq : secondGross=gross^2) : siFundVarianceNext v m c gross secondGross=0 := by
  unfold siFundVarianceNext siFundSecondNext siFundMeanNext
  rw [hv, hq]
  ring
