-- Prove2me | Definitions.Def_Kyprianou_Ch09_RussianExpectation
-- name    : Kyprianou_Ch09_RussianExpectation
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:14:56.529044+00:00
-- url     : https://prove2.me/theorems/d7c6e832-99b2-4dbd-8023-b962590a24a1
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner RussianExpectation
-- statement:
--   Discounted running-supremum reward expectation definitions. This source Definition module provides the actual declarations: RussianExpectation. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_RussianImmediate
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- At any finite, integrable random time, the true expected Russian
reward is bounded by the immediate reward. The stronger pointwise
inequality applies to every almost surely finite stopping time. -/
theorem russianExpectedReward_le_initial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (q d x : ℝ) (S : ℝ → Ω → ℝ) (τ : Ω → ℝ)
    (hd : 0 ≤ d) (hq : d ≤ q) (hx : 0 ≤ x)
    (hτ : ∀ ω, 0 ≤ τ ω)
    (hS : ∀ ω s, 0 ≤ s → 0 ≤ S s ω)
    (hInt : Integrable (russianRandomReward q d x S τ) P) :
    (∫ ω, russianRandomReward q d x S τ ω ∂P) ≤ Real.exp x := by
  have hevent : ∀ᵐ ω ∂P,
      russianRandomReward q d x S τ ω ≤ Real.exp x :=
    Filter.Eventually.of_forall
      (russianRandomReward_le_immediate q d x S τ hd hq hx hτ hS)
  have hle := integral_mono_ae hInt (integrable_const (Real.exp x)) hevent
  simpa using hle

/-- The expected immediate reward equals exp(x) when X_0=0. -/
theorem russianExpectedImmediate_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (q d x : ℝ) (S : ℝ → Ω → ℝ)
    (hx : 0 ≤ x) (hSzero : ∀ ω, S 0 ω = 0) :
    (∫ ω, russianRandomReward q d x S (fun _ => 0) ω ∂P) =
      Real.exp x := by
  have hfun :
      (fun ω => russianRandomReward q d x S (fun _ => 0) ω) =
       (fun _ : Ω => Real.exp x) := by
    funext ω
    exact russianImmediateReward_eq q d x S ω hx (hSzero ω)
  rw [hfun]
  simp

end Kyprianou.Ch09.B1


