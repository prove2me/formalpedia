-- Prove2me | solution 1 for ActuarialValuation.pen9DCFund_add_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:21.691978+00:00
-- url     : https://prove2.me/submissions/b7b1b75d-4c2c-4b06-b47c-f93677c1e48b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pen9DCFund

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c₁ c₂ : ℝ) (s : ℕ → ℝ) (j : ℝ) (n : ℕ) : pen9DCFund (c₁+c₂) s j n = pen9DCFund c₁ s j n + pen9DCFund c₂ s j n := by
  unfold pen9DCFund
  ring
