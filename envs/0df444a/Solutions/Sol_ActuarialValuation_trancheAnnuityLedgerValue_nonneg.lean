-- Prove2me | solution 1 for ActuarialValuation.trancheAnnuityLedgerValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:07:18.612507+00:00
-- url     : https://prove2.me/submissions/2db14ccc-de20-410a-9d94-2ac469f8acd7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_trancheAnnuityLedgerValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℕ → ℝ) (i H : ℕ)
  (hw : ∀ k ∈ Finset.range H, 0 ≤ w i k) :
  0 ≤ trancheAnnuityLedgerValue w i H := by
  unfold trancheAnnuityLedgerValue
  apply Finset.sum_nonneg
  intro k hk
  exact hw k hk
