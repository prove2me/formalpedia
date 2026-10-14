-- Prove2me | solution 1 for ActuarialValuation.svTermInsurance_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:50.638107+00:00
-- url     : https://prove2.me/submissions/216b0ad9-2bfe-4ed3-83aa-71e97b0600f0

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTermInsurance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p d : ℕ → ℝ) (n : ℕ) (a : ℝ) : svFiniteTermInsurance (fun k => a*p k) d n = a * svFiniteTermInsurance p d n := by
  unfold svFiniteTermInsurance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
