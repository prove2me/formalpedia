-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F000
-- name    : LevyStochCalc_Poisson_CharacterMarkFactor_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:03:48.019821+00:00
-- url     : https://prove2.me/theorems/3559a103-302c-4a97-ae3d-acea222856c4
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterMarkFactor
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterMarkFactor. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F002
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The deterministic mark factor of the chain rule's integrand

At each time and mark the chain rule's integrand is the product of a deterministic factor,
carrying the indicator of the family and the jump `e^{i m} - 1` that a point there contributes,
with the exponential of the strict past. Inside the window the second factor agrees almost
surely with the character at that time, and so does the predictable representative of the
strict-past character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section MarkFactor

/-- The deterministic factor of the chain rule's integrand at a time and a mark. -/
noncomputable def markFactor (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) : ℂ :=
  (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (simpleMark w Bfam q : ℂ)) - 1)
variable (N : PoissonRandomMeasure P ν)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The chain rule's integrand is the mark factor times the exponential of the strict past. -/
theorem charIntegrand_eq_markFactor_mul (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E)
    (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    charIntegrand N w Bfam A T ω s e
      = markFactor w Bfam (s, e)
        * Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ)) := by
  rw [charIntegrand, markFactor]
  ring
end MarkFactor

end LevyStochCalc.Poisson


