-- Prove2me | solution 1 for ActuarialValuation.ratPortfolioPremium_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:48:53.160232+00:00
-- url     : https://prove2.me/submissions/d154d873-0b68-4785-a4f4-1b2d2aa83235

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_ratWeightedExposure
import Definitions.Def_actuarial_ratPortfolioPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e r : ℕ → ℝ) (n : ℕ) (base : ℝ) :
    ratPortfolioPremium e r n base = base * ratWeightedExposure e r n := by
  simp only [ratPortfolioPremium, ratClassPremium, ratWeightedExposure]
  calc
    (∑ i ∈ Finset.range n, e i * base * r i)
        = ∑ i ∈ Finset.range n, (e i * r i) * base := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (e i * base) * r i = e i * (base * r i) := mul_assoc _ _ _
              _ = e i * (r i * base) := congrArg (fun x : ℝ => e i * x) (mul_comm base (r i))
              _ = (e i * r i) * base := (mul_assoc _ _ _).symm
    _ = (∑ i ∈ Finset.range n, e i * r i) * base := by
          rw [← Finset.sum_mul]
    _ = base * ∑ i ∈ Finset.range n, e i * r i := mul_comm _ _
