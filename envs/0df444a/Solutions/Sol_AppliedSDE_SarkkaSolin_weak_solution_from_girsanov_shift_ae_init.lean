-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.weak_solution_from_girsanov_shift_ae_init
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:31:22.138404+00:00
-- url     : https://prove2.me/submissions/dbcc633c-f0df-4777-8d86-4fd5d80f8c03

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (x₀ : ℝ) (f : ℝ → ℝ → ℝ)
    (hInt : ∀ (t : ℝ≥0) (ω : Ω), IntegrableOn
      (fun s : ℝ => f (x₀ + W.W s ω) s)
      (Set.Icc (0 : ℝ) (t : ℝ)))
    (hBrownian : IsBrownianReal
      (fun (t : ℝ≥0) (ω : Ω) =>
        W.W (t : ℝ) ω -
          ∫ s in (0 : ℝ)..(t : ℝ), f (x₀ + W.W s ω) s) Q) :
    let X : ℝ → Ω → ℝ := fun t ω => x₀ + W.W t ω
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω -
        ∫ s in (0 : ℝ)..(t : ℝ), f (X s ω) s
    (∀ᵐ ω ∂P, X 0 ω = x₀) ∧
    (∀ (t : ℝ≥0) (ω : Ω),
      X t ω = x₀ + (∫ s in (0 : ℝ)..(t : ℝ),
        f (X s ω) s) + shifted t ω) := by
  dsimp only
  constructor
  · filter_upwards [W.initial_zero] with ω hω
    simp [hω]
  · intro t ω
    ring
