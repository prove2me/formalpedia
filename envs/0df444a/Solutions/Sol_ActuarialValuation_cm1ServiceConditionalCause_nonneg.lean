-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceConditionalCause_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:22:02.616355+00:00
-- url     : https://prove2.me/submissions/cd4ece83-561e-4aa6-a452-5245e59c86f0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceConditionalCause
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (t j : ℕ) (hl : 0 < l t) (hd : 0 ≤ d t j) : 0 ≤ cm1ServiceConditionalCause l d t j := by
  unfold cm1ServiceConditionalCause
  exact div_nonneg hd (le_of_lt hl)
