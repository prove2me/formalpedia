-- Prove2me | solution 1 for ActuarialValuation.cm1LifeMortality_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:09.440494+00:00
-- url     : https://prove2.me/submissions/3fad15d4-cd03-48bb-8cc0-06cc2ad93be8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeMortality
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) (hl : 0 < l x) (hle : l (x+n) ≤ l x) : 0 ≤ cm1LifeMortality l x n := by
  unfold cm1LifeMortality cm1LifeSurvival
  have h : l (x + n) / l x ≤ 1 := (div_le_one hl).2 hle
  linarith
