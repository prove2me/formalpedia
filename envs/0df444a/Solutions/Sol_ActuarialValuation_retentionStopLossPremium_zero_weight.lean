-- Prove2me | solution 1 for ActuarialValuation.retentionStopLossPremium_zero_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:46.934996+00:00
-- url     : https://prove2.me/submissions/4350e630-0b5f-42b2-8f8a-9591e26c550d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (X : ℕ → ℝ) (B : ℕ) (d : ℝ) :
  retentionStopLossPremium (fun _ => 0) X B d = 0 := by
  simp [retentionStopLossPremium]
