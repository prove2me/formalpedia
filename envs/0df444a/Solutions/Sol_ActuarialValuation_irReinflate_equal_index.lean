-- Prove2me | solution 1 for ActuarialValuation.irReinflate_equal_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:57:29.996985+00:00
-- url     : https://prove2.me/submissions/361f1092-bbbe-4800-9c7e-ce575be78271

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irReinflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim index : ℝ) (hi : index≠0) : irReinflate claim index index=claim := by
  unfold irReinflate
  field_simp [hi]
