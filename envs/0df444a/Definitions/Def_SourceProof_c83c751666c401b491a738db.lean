-- Prove2me | Definitions.Def_SourceProof_c83c751666c401b491a738db
-- name    : SourceProof_c83c751666c401b491a738db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:07:08.43351+00:00
-- url     : https://prove2.me/theorems/58d21f26-7236-47ba-864a-eafde76e8c41
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.BrownianMotion.exists
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Existence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion from a pre-Brownian process

A process `X : ℝ≥0 → Ω → ℝ` with the finite-dimensional laws of Brownian motion
(`ProbabilityTheory.IsPreBrownianReal`), measurable marginals and continuous paths yields a
`BrownianMotion P` in the sense of `LevyStochCalc.Brownian.Construction`: extend to real time by
`t ↦ X (t⁺) − X 0`, which vanishes at non-positive times and is re-centred at the origin. The weak
Markov property `ProbabilityTheory.IsPreBrownianReal.indepFun_shift` supplies the σ-algebra
independence of the past from a future increment.

## Main statements

* `BrownianMotion.ofIsPreBrownianReal` — the construction.
* `BrownianMotion.exists` — existence, from the canonical Brownian motion `brownian` on
  `gaussianLimit`, lifted to an arbitrary universe.
-/

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_c83c751666c401b491a738db :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P) := by
  let e : ULift.{u} (ℝ≥0 → ℝ) ≃ᵐ (ℝ≥0 → ℝ) := MeasurableEquiv.ulift
  let P : Measure (ULift.{u} (ℝ≥0 → ℝ)) := gaussianLimit.map e.symm
  have hP : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  have hdown : HasLaw e gaussianLimit P :=
    ⟨e.measurable.aemeasurable, by simp [P, Measure.map_map e.measurable e.symm.measurable]⟩
  refine ⟨ULift.{u} (ℝ≥0 → ℝ), inferInstance, P, hP, ⟨?_⟩⟩
  refine LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal (X := fun t ω => brownian t (e ω)) ?_ ?_ ?_
  · exact ⟨fun I => (isBrownianReal_brownian.hasLaw I).comp hdown⟩
  · exact fun t => (measurable_brownian t).comp e.measurable
  · exact fun ω => continuous_brownian (e ω)
end LevyStochCalc.Brownian


