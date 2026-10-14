-- Prove2me | solution 1 for ActuarialValuation.crRisk_portfolio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:59:33.706697+00:00
-- url     : https://prove2.me/submissions/06b12821-31c3-4b01-8284-8afc2fd472a0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crPortfolioLoss

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X Y : Fin n→ℝ) : crScenarioRisk p q (crPortfolioLoss X Y) ≤ crScenarioRisk p q X + crScenarioRisk p q Y := by
  unfold crPortfolioLoss
  unfold crScenarioRisk
  simp only [crExpected, mul_add, Finset.sum_add_distrib]
  apply max_le
  · have h1 := le_max_left (∑ i : Fin n, p i * X i) (∑ i : Fin n, q i * X i)
    have h2 := le_max_left (∑ i : Fin n, p i * Y i) (∑ i : Fin n, q i * Y i)
    linarith
  · have h1 := le_max_right (∑ i : Fin n, p i * X i) (∑ i : Fin n, q i * X i)
    have h2 := le_max_right (∑ i : Fin n, p i * Y i) (∑ i : Fin n, q i * Y i)
    linarith
