-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F003
-- name    : LevyStochCalc_Poisson_CompensatorL1_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:20:30.839183+00:00
-- url     : https://prove2.me/theorems/e4257f8e-682e-4453-b0e7-c0dfcad51afb
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatorL1
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatorL1. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

/-- The pathwise compensated integral is additive on integrands integrable on the window. -/
theorem pathwise_sub {η₁ η₂ : Ω → ℝ → E → ℝ} (ω : Ω)
    (h1 : IntegrableOn (fun q : ℝ × E => η₁ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω))
    (h1' : IntegrableOn (fun q : ℝ × E => η₁ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (referenceIntensity ν))
    (h2 : IntegrableOn (fun q : ℝ × E => η₂ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω))
    (h2' : IntegrableOn (fun q : ℝ × E => η₂ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (referenceIntensity ν)) :
    ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₁ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₁ ω q.1 q.2 ∂(referenceIntensity ν))
      - ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₂ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₂ ω q.1 q.2 ∂(referenceIntensity ν))
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (η₁ ω q.1 q.2 - η₂ ω q.1 q.2) ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            (η₁ ω q.1 q.2 - η₂ ω q.1 q.2) ∂(referenceIntensity ν) := by
  rw [integral_sub h1 h2, integral_sub h1' h2']
  ring
end Pathwise

end LevyStochCalc.Poisson


