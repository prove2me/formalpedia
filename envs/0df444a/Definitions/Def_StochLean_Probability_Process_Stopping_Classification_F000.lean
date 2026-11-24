-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Classification_F000
-- name    : StochLean_Probability_Process_Stopping_Classification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:01.970904+00:00
-- url     : https://prove2.me/theorems/863e8962-bb94-4ff1-aed9-f4d9647b6e93
-- title:
--   StochLean: Probability.Process.Stopping.Classification F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Accessible and totally inaccessible stopping times

Protter III.2 uses countable predictable coverage of the finite graph for
accessibility and null intersection with every predictable finite graph for
total inaccessibility. The almost-sure coverage formulation also works for
arbitrary measures. Infinite times are excluded from all coincidence tests.

These predicates and their elementary consequences do not by themselves prove
the general accessible/totally-inaccessible decomposition of Protter III.3.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Countably many predictable stopping times cover the finite graph almost surely. -/
def IsAccessibleStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∃ σ : ℕ → Ω → WithTop ℝ≥0,
    (∀ n, IsPredictableStoppingTime F (σ n) P) ∧
      ∀ᵐ ω ∂P, τ ω ≠ ⊤ → ∃ n, τ ω = σ n ω
/-- Every predictable finite graph meets this graph on a null event. -/
def IsTotallyInaccessibleStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∀ σ : Ω → WithTop ℝ≥0, IsPredictableStoppingTime F σ P →
    P {ω | τ ω = σ ω ∧ τ ω ≠ ⊤} = 0
variable {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {P : Measure Ω}

end ProbabilityTheory


