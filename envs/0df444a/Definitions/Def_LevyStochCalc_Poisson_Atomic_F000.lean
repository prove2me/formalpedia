-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
-- name    : LevyStochCalc_Poisson_Atomic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:17:52.227952+00:00
-- url     : https://prove2.me/theorems/1cf5b480-4bf3-4a0a-ac55-88ab791e942c
-- title:
--   Source declarations: LevyStochCalc.Poisson.Atomic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Atomic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
import Definitions.Def_SourceProof_adf2db00933ba5955625daf4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Atomicity of a Poisson random measure on a finite-activity window

A Poisson random measure carries a natural mass on each measurable set of finite intensity, one
set at a time and only almost surely. Over a window of finite intensity the counts on a countable
generating π-system are simultaneously natural on a single event of full measure, and the sets of
natural mass form a Dynkin system, so on that event the restricted measure is integer-valued. On
a countably separated mark space it is then a finite sum of Dirac masses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section CountablyGenerated

variable [MeasurableSpace.CountablyGenerated E]

/-- A countable π-system generating the σ-algebra of the time–mark space. -/
noncomputable def markPiSystem (E : Type v) [MeasurableSpace E]
    [MeasurableSpace.CountablyGenerated E] : Set (Set (ℝ × E)) :=
  Probability.finInters (MeasurableSpace.natGeneratingSequence (ℝ × E))
theorem generateFrom_markPiSystem :
    MeasurableSpace.generateFrom (markPiSystem E)
      = (inferInstance : MeasurableSpace (ℝ × E)) := by
  rw [markPiSystem, Probability.generateFrom_finInters,
    MeasurableSpace.generateFrom_natGeneratingSequence]
theorem isPiSystem_markPiSystem : IsPiSystem (markPiSystem E) :=
  _root_.Prove2MeSourceProof.h_adf2db00933ba5955625daf4 _
end CountablyGenerated

section Atomic

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Atomic

end LevyStochCalc.Poisson


