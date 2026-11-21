-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F000
-- name    : LevyStochCalc_Poisson_CharacterFubini_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:55:15.960719+00:00
-- url     : https://prove2.me/theorems/428bd035-ff11-42a4-9633-30329d62d4f5
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterFubini
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterFubini. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrict_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

/-- The deterministic factor of the chain rule's integrand for the family cut at `t`. -/
noncomputable def charMark (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) : ℂ :=
  (((⋃ j, truncFam Bfam t j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (simpleMark w (truncFam Bfam t) q : ℂ)) - 1)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charIntegrand_truncFam_eq (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T t : ℝ) (ω : Ω) (q : ℝ × E) :
    charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2
      = charMark w Bfam t q
        * Complex.exp (Complex.I * (predStrict N w (truncFam Bfam t) A T ω q.1 q.2 : ℂ)) := by
  simp only [charIntegrand, charMark, Prod.mk.eta]
  ring
end Fubini

end LevyStochCalc.Poisson


