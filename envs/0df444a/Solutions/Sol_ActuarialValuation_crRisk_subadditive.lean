-- Prove2me | solution 1 for ActuarialValuation.crRisk_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:38.415481+00:00
-- url     : https://prove2.me/submissions/523cfb60-9ab3-4efa-b443-34b3d1934e21

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X Y : Fin n→ℝ) : crScenarioRisk p q (fun i=>X i+Y i) ≤ crScenarioRisk p q X+crScenarioRisk p q Y := by
  have he1 : crExpected p (fun i => X i + Y i) =
      crExpected p X + crExpected p Y := by
    unfold crExpected
    simp only [mul_add, Finset.sum_add_distrib]
  have he2 : crExpected q (fun i => X i + Y i) =
      crExpected q X + crExpected q Y := by
    unfold crExpected
    simp only [mul_add, Finset.sum_add_distrib]
  unfold crScenarioRisk
  rw [he1, he2]
  apply max_le
  · have h1 := le_max_left (crExpected p X) (crExpected q X)
    have h2 := le_max_left (crExpected p Y) (crExpected q Y)
    linarith
  · have h1 := le_max_right (crExpected p X) (crExpected q X)
    have h2 := le_max_right (crExpected p Y) (crExpected q Y)
    linarith
