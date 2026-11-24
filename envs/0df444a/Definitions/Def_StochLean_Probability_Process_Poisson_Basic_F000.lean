-- Prove2me | Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
-- name    : StochLean_Probability_Process_Poisson_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:08.713972+00:00
-- url     : https://prove2.me/theorems/cc548a7f-d054-41cb-b47d-d992cbc4cfce
-- title:
--   StochLean: Probability.Process.Poisson.Basic F000

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_StationaryIncrements_F000
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Poisson processes

The predicate below packages the standard counting-process requirements without introducing a
new process type. Path properties use one common almost-sure event, and increment laws are only
asserted for ordered times, where natural subtraction represents an actual count increment.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A rate-`rate` Poisson process on nonnegative real time. -/
structure IsPoissonProcess (X : NNReal → Ω → ℕ) (rate : NNReal)
    (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] : Prop where
  aemeasurable : ∀ t, AEMeasurable (X t) P
  initial : X 0 =ᵐ[P] fun _ ↦ 0
  monotonePaths : HasMonotonePaths X P
  rightContinuousPaths : HasRightContinuousPaths X P
  indepIncrements : HasIndepIncrements X P
  incrementLaw : ∀ s t, s ≤ t →
    HasLaw (fun ω ↦ X t ω - X s ω) (poissonMeasure (rate * (t - s))) P
namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

end IsPoissonProcess

end ProbabilityTheory


