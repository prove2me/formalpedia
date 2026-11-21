-- Prove2me | Definitions.Def_SourceProof_64e5e836994ceb2ae7c553a4
-- name    : SourceProof_64e5e836994ceb2ae7c553a4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:30:39.269518+00:00
-- url     : https://prove2.me/theorems/437ec425-8674-479a-a196-63eaf47bbd29
-- title:
--   LevyStochCalc source module: SourceProof_64e5e836994ceb2ae7c553a4
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_sub_integral` comes from the `LevyStochCalc.Poisson.MarkStepPathwise` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-step approximants are pathwise and predictable

The approximants the compensated integral is built from are finite combinations of indicators of
time–mark rectangles with coefficients known at the left endpoint of their piece. Their integral
against any measure finite on those rectangles is the matching finite combination, so over the
whole horizon the approximant's compensated integral is the difference of its integrals against
the random measure and against the reference intensity. Adaptedness of the coefficients makes the
approximant predictable, which is what the compensator identity asks for.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {g : TimeGrid}

namespace MarkStep


theorem _root_.Prove2MeSourceProof.h_64e5e836994ceb2ae7c553a4 (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ω : Ω) (hfin : ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤) :
    G.integral N t ω
      = (∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω ∂(N.N ω))
        - ∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω
            ∂(referenceIntensity ν) := by
  have hIfin : ∀ i (k : Fin G.K),
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤ :=
    fun i k => LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _
  rw [G.integral_evalTo_eq_sum t (N.N ω) hfin ω,
    G.integral_evalTo_eq_sum t (LevyStochCalc.Poisson.referenceIntensity ν) hIfin ω, ← Finset.sum_sub_distrib,
    LevyStochCalc.Poisson.Compensated.MarkStep.integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  ring
section RestrictMarks

variable {A : Set E}

end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated


