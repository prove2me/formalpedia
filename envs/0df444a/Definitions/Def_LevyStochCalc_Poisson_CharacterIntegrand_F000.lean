-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F000
-- name    : LevyStochCalc_Poisson_CharacterIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:28.001683+00:00
-- url     : https://prove2.me/theorems/49e12f87-8b72-453d-9c72-dd8284d844ab
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleCharacter_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

/-- The integrand of the jump chain rule, in its predictable form. -/
noncomputable def charIntegrand (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℂ :=
  (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ) *
    (Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ))
      * (Complex.exp (Complex.I * (simpleMark w Bfam (s, e) : ℂ)) - 1))
/-- The real part of the chain rule's integrand. -/
noncomputable def charRe (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ := (charIntegrand N w Bfam A T ω s e).re
/-- The imaginary part of the chain rule's integrand. -/
noncomputable def charIm (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ := (charIntegrand N w Bfam A T ω s e).im
end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Assembly

end LevyStochCalc.Poisson


