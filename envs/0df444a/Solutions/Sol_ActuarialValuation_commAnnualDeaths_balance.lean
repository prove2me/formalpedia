-- Prove2me | solution 1 for ActuarialValuation.commAnnualDeaths_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:34.325734+00:00
-- url     : https://prove2.me/submissions/3ac6152b-b33d-47ce-9ae8-a6d81a5c7886

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commAnnualDeaths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x : ℕ) : commAnnualDeaths l x + l (x+1) = l x := by
  unfold commAnnualDeaths
  exact sub_add_cancel (l x) (l (x+1))
