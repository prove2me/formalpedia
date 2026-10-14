-- Prove2me | solution 1 for ActuarialValuation.pfAmortisation_clears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:33:50.96799+00:00
-- url     : https://prove2.me/submissions/87781aca-ad29-4b51-bf38-a4182780a6e6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAmortisation
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (deficit annuity : ℝ) (h : annuity≠0) : pfAmortisation deficit annuity*annuity=deficit := by
  unfold pfAmortisation
  field_simp [h]
