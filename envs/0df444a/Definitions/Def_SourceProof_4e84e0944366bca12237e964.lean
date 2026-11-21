-- Prove2me | Definitions.Def_SourceProof_4e84e0944366bca12237e964
-- name    : SourceProof_4e84e0944366bca12237e964
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:29:00.736183+00:00
-- url     : https://prove2.me/theorems/27e6dad1-c820-481a-8d2c-4e81b2194d26
-- title:
--   LevyStochCalc source module: SourceProof_4e84e0944366bca12237e964
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_evalTo` comes from the `LevyStochCalc.Poisson.MarkStepPathwise` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_4e84e0944366bca12237e964 (G : MarkStep Ω E ν g)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) (t : ℝ) :
    Probability.MarkedPredictable ℱ ν
      fun ω s e => (Set.Iic t).indicator (fun _ => (1 : ℝ)) s * G.eval s e ω := by
  classical
  have hterm : ∀ i, i < g.N₀ → ∀ k : Fin G.K,
      Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 := by
    intro i hi k
    rcases le_or_gt (min (g.p (i + 1)) t) (min (g.p i) t) with hle | hlt
    · have hempty : Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt.mpr hle)
      have hzero : (fun p : Ω × ℝ × E =>
          (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
            (fun _ : ℝ × E => G.ξ i k p.1) p.2) = fun _ => (0 : ℝ) := by
        funext p
        rw [hempty, Set.empty_prod, Set.indicator_empty]
      rw [hzero]
      exact measurable_const
    · have hmin : min (g.p i) t = g.p i := by
        refine min_eq_left ?_
        by_contra hcon
        have hti : t < g.p i := not_le.mp hcon
        rw [min_eq_right hti.le] at hlt
        exact absurd (lt_of_lt_of_le hlt (min_le_right (g.p (i + 1)) t)) (lt_irrefl t)
      intro U hU
      have hξU : MeasurableSet[ℱ (min (g.p i) t)] (G.ξ i k ⁻¹' U) := by
        rw [hmin]
        exact (hG i hi k).measurable hU
      have hnn : 0 ≤ min (g.p i) t := by rw [hmin]; exact g.p_nonneg hi.le
      have hbig : MeasurableSet[LevyStochCalc.Probability.markedPredictableSigma ℱ ν]
          ((G.ξ i k ⁻¹' U) ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)) :=
        MeasurableSpace.measurableSet_generateFrom
          ⟨min (g.p i) t, min (g.p (i + 1)) t, _, _, hnn, hξU, G.B_measurable k,
            G.B_finite k, rfl⟩
      have huniv : MeasurableSet[LevyStochCalc.Probability.markedPredictableSigma ℱ ν]
          ((Set.univ : Set Ω) ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)) :=
        MeasurableSpace.measurableSet_generateFrom
          ⟨min (g.p i) t, min (g.p (i + 1)) t, _, _, hnn, MeasurableSet.univ,
            G.B_measurable k, G.B_finite k, rfl⟩
      by_cases h0 : (0 : ℝ) ∈ U
      · have hset : (fun p : Ω × ℝ × E =>
            (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
              (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
            = ((G.ξ i k ⁻¹' U)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k))
              ∪ ((Set.univ : Set Ω)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k))ᶜ := by
          ext p
          by_cases hp : p.2 ∈ Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k
          · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact Or.inl (Set.mem_prod.mpr ⟨h, hp⟩)
            · intro h
              rw [Set.mem_preimage, hL]
              rcases h with h | h
              · exact (Set.mem_prod.mp h).1
              · exact absurd (Set.mem_prod.mpr ⟨Set.mem_univ p.1, hp⟩) h
          · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro _
              exact Or.inr fun h => hp (Set.mem_prod.mp h).2
            · intro _
              rw [Set.mem_preimage, hL]
              exact h0
        rw [hset]
        exact hbig.union huniv.compl
      · have hset : (fun p : Ω × ℝ × E =>
            (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
              (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
            = (G.ξ i k ⁻¹' U)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) := by
          ext p
          by_cases hp : p.2 ∈ Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k
          · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact Set.mem_prod.mpr ⟨h, hp⟩
            · intro h
              rw [Set.mem_preimage, hL]
              exact (Set.mem_prod.mp h).1
          · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact absurd h h0
            · intro h
              exact absurd (Set.mem_prod.mp h).2 hp
        rw [hset]
        exact hbig
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun _ => (1 : ℝ)) p.2.1 * G.eval p.2.1 p.2.2 p.1)
      = fun p : Ω × ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 :=
    funext fun p => G.evalTo_eq_sum_indicator t p.2 p.1
  change Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] _
  rw [hrw]
  exact Finset.measurable_sum _ fun i hi =>
    Finset.measurable_sum _ fun k _ => hterm i (Finset.mem_range.mp hi) k
section RestrictMarks

variable {A : Set E}

end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated


