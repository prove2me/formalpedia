-- Prove2me | Definitions.Def_SourceProof_a108b20c3c7f7ed49b14b48f
-- name    : SourceProof_a108b20c3c7f7ed49b14b48f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:48:41.228601+00:00
-- url     : https://prove2.me/theorems/efb8f316-d42e-446b-81ff-9865c3ff061c
-- title:
--   LevyStochCalc source module: SourceProof_a108b20c3c7f7ed49b14b48f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_markedStopped` comes from the `LevyStochCalc.Ito.CompensatedLocalityCutoff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000
import Definitions.Def_SourceProof_0efef36d22ac9421e0560dc4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}


theorem _root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f (hτ : IsStoppingTime ℱ τ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (markedStopped τ φ) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  set R : Set (Ω × ℝ × E) :=
    {p | (p.1, p.2.1) ∈ LevyStochCalc.Probability.stoppedRegion τ t} with hR
  have key : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => LevyStochCalc.Poisson.Compensated.markedStopped τ φ p.1 s p.2.2) p.2.1)
      = R.indicator fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
    funext p
    by_cases h1 : p ∈ R
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ R from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2.1 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2.1 ∈ Set.Iic t from h1a), LevyStochCalc.Poisson.Compensated.markedStopped_of_le τ φ h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2.1 ∈ Set.Iic t
      · have h3 : ¬ ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, LevyStochCalc.Poisson.Compensated.markedStopped_of_not_le τ φ h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hp t).indicator ((_root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 hτ t).preimage
    (measurable_fst.prodMk measurable_snd.fst))
end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

end Transport

end LevyStochCalc.Poisson.Compensated


