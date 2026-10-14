-- Prove2me | solution 1 for ActuarialValuation.irDeflate_equal_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:57:12.245986+00:00
-- url     : https://prove2.me/submissions/40041785-8b77-49c0-b12d-ea391181e3a8

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim index : ℝ) (hi : index≠0) : irDeflate claim index index=claim := by
  unfold irDeflate
  field_simp [hi]
