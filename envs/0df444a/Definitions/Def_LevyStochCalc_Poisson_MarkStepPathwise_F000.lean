-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F000
-- name    : LevyStochCalc_Poisson_MarkStepPathwise_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:39:26.046339+00:00
-- url     : https://prove2.me/theorems/f2f0eeee-d372-4b6c-89bd-ec66bb6ea9a7
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepPathwise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepPathwise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F003

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

/-- The mark-step integrand as a finite combination of rectangle indicators. -/
theorem eval_eq_sum_indicator (G : MarkStep Ω E ν g) (q : ℝ × E) (ω : Ω) :
    G.eval q.1 q.2 ω = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
      (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator (fun _ : ℝ × E => G.ξ i k ω) q := by
  classical
  rw [MarkStep.eval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hs : q.1 ∈ Set.Ioc (g.p i) (g.p (i + 1))
  · by_cases he : q.2 ∈ G.B k
    · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hs, he⟩), Set.indicator_of_mem hs,
        Set.indicator_of_mem he]
      ring
    · rw [Set.indicator_of_notMem (fun h => he (Set.mem_prod.mp h).2),
        Set.indicator_of_notMem he]
      ring
  · rw [Set.indicator_of_notMem (fun h => hs (Set.mem_prod.mp h).1),
      Set.indicator_of_notMem hs]
    ring
/-- The integral of a mark-step integrand against a measure finite on its rectangles. -/
theorem integral_eval_eq_sum (G : MarkStep Ω E ν g) (μ : Measure (ℝ × E))
    (hfin : ∀ i k, μ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤) (ω : Ω) :
    ∫ q, G.eval q.1 q.2 ω ∂μ
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
          (μ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k)).toReal * G.ξ i k ω := by
  classical
  have hrectm : ∀ i (k : Fin G.K),
      MeasurableSet (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) :=
    fun i k => measurableSet_Ioc.prod (G.B_measurable k)
  have hrw : (fun q : ℝ × E => G.eval q.1 q.2 ω)
      = fun q : ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q := funext fun q => G.eval_eq_sum_indicator q ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hrectm i k), smul_eq_mul, measureReal_def]
    · intro k _
      rw [integrable_indicator_iff (hrectm i k)]
      exact integrableOn_const (hfin i k)
  · intro i _
    refine integrable_finsetSum _ fun k _ => ?_
    rw [integrable_indicator_iff (hrectm i k)]
    exact integrableOn_const (hfin i k)
/-- **The mark-step compensated integral over the horizon is pathwise.** -/
theorem full_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (ω : Ω)
    (hfin : ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤) :
    G.full N ω = (∫ q, G.eval q.1 q.2 ω ∂(N.N ω))
      - ∫ q, G.eval q.1 q.2 ω ∂(referenceIntensity ν) := by
  have hIfin : ∀ i (k : Fin G.K),
      referenceIntensity ν (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤ :=
    fun i k => referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _
  rw [G.integral_eval_eq_sum (N.N ω) hfin ω,
    G.integral_eval_eq_sum (referenceIntensity ν) hIfin ω, ← Finset.sum_sub_distrib,
    MarkStep.full]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PoissonRandomMeasure.compensated]
  ring
/-- A time interval cut at `t` is the interval between the cut endpoints. -/
theorem Ioc_inter_Iic (a b t : ℝ) :
    Set.Ioc a b ∩ Set.Iic t = Set.Ioc (min a t) (min b t) := by
  ext x
  have hnot : x ≤ t → ¬ t < x := fun h => not_lt.mpr h
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, min_lt_iff, le_min_iff]
  tauto
/-- The rectangle of a mark-step integrand cut at `t`. -/
theorem fullRect_inter_Iic (G : MarkStep Ω E ν g) (i : ℕ) (k : Fin G.K) (t : ℝ) :
    (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ∩ (Set.Iic t ×ˢ (Set.univ : Set E))
      = Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k := by
  rw [Set.prod_inter_prod, Ioc_inter_Iic, Set.inter_univ]
/-- The mark-step integrand cut at `t`, as a finite combination of cut-rectangle indicators. -/
theorem evalTo_eq_sum_indicator (G : MarkStep Ω E ν g) (t : ℝ) (q : ℝ × E) (ω : Ω) :
    (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q := by
  classical
  rw [G.eval_eq_sum_indicator q ω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← G.fullRect_inter_Iic i k t]
  by_cases hq : q.1 ∈ Set.Iic t
  · rw [Set.indicator_of_mem hq, one_mul]
    by_cases hr : q ∈ Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k
    · rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (Set.mem_inter hr (Set.mem_prod.mpr ⟨hq, Set.mem_univ q.2⟩))]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem fun h => hr h.1]
  · rw [Set.indicator_of_notMem hq, zero_mul,
      Set.indicator_of_notMem fun h => hq (Set.mem_prod.mp h.2).1]
/-- The integral of a cut mark-step integrand against a measure finite on the cut rectangles. -/
theorem integral_evalTo_eq_sum (G : MarkStep Ω E ν g) (t : ℝ) (μ : Measure (ℝ × E))
    (hfin : ∀ i (k : Fin G.K),
      μ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤) (ω : Ω) :
    ∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω ∂μ
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
          (μ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)).toReal * G.ξ i k ω := by
  classical
  have hrectm : ∀ i (k : Fin G.K),
      MeasurableSet (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) :=
    fun i k => measurableSet_Ioc.prod (G.B_measurable k)
  have hrw : (fun q : ℝ × E =>
        (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω)
      = fun q : ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q :=
    funext fun q => G.evalTo_eq_sum_indicator t q ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hrectm i k), smul_eq_mul, measureReal_def]
    · intro k _
      rw [integrable_indicator_iff (hrectm i k)]
      exact integrableOn_const (hfin i k)
  · intro i _
    refine integrable_finsetSum _ fun k _ => ?_
    rw [integrable_indicator_iff (hrectm i k)]
    exact integrableOn_const (hfin i k)
section RestrictMarks

variable {A : Set E}

end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated


