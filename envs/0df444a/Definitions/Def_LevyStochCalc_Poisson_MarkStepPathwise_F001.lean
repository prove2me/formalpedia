-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F001
-- name    : LevyStochCalc_Poisson_MarkStepPathwise_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:41:22.532723+00:00
-- url     : https://prove2.me/theorems/cab79417-5346-454a-8365-efc43a66b7b1
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepPathwise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepPathwise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The counts on the rectangles of a mark-step integrand are almost surely finite. -/
theorem ae_count_rect_ne_top (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) :
    ∀ᵐ ω ∂P, ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤ := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  filter_upwards [N.integer_valued (measurableSet_Ioc.prod (G.B_measurable k))
    (referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _)] with ω hω
  obtain ⟨n, hn⟩ := hω
  rw [hn]
  exact ENNReal.natCast_ne_top n
/-- The counts on the clamped rectangles are almost surely finite. -/
theorem ae_count_clamped_rect_ne_top (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
    (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤ := by
  filter_upwards [ae_count_rect_ne_top N G] with ω hω i k
  refine ne_top_of_le_ne_top (hω i k) (measure_mono ?_)
  rw [← G.fullRect_inter_Iic i k t]
  exact Set.inter_subset_left
/-- The pathwise form of the mark-step compensated integral, almost surely. -/
theorem ae_full_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) :
    ∀ᵐ ω ∂P, G.full N ω = (∫ q, G.eval q.1 q.2 ω ∂(N.N ω))
      - ∫ q, G.eval q.1 q.2 ω ∂(referenceIntensity ν) := by
  filter_upwards [ae_count_rect_ne_top N G] with ω hω
  exact full_eq_sub_integral N G ω hω
section RestrictMarks

variable {A : Set E}

end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated


