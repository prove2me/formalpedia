-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_full_guarantee_certain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:49:06.400266+00:00
-- url     : https://prove2.me/submissions/c1c558c8-7e1a-42cd-b6e0-ad5ad7bbd3d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcCertainPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialAnnuitiesContinuous

theorem solution (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ)
    (a term g rho : ℝ) (b : ℝ → ℝ)
    (hn : 0 ≤ term) (hg : term ≤ g)
    (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t))
      volume a (a+term)) :
    bcProjectedPV N p life a term g rho b =
      bcSurvival N p life a * bcCertainPV a term rho b := by
  have hab : a ≤ a+term := by linarith
  have hne : ∀ᵐ (t : ℝ) ∂volume, t ≠ a+term :=
    Measure.ae_ne volume (a+term)
  have heq :
      (∫ t in a..(a+term), b t * Real.exp (-rho*t) *
        (if t < a+g then bcSurvival N p life a
         else bcSurvival N p life t)) =
      (∫ t in a..(a+term), b t * Real.exp (-rho*t) *
        bcSurvival N p life a) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with t ht htmem
    have hmem : t ∈ Set.Ioc a (a+term) := by
      simpa only [Set.uIoc_of_le hab] using htmem
    have hlt : t < a+g := by
      have hstrict : t < a+term := lt_of_le_of_ne hmem.2 ht
      linarith
    simp [hlt]
  unfold bcProjectedPV bcCertainPV
  rw [heq, intervalIntegral.integral_mul_const]
  ring
