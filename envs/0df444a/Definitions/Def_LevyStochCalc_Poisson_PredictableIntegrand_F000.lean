-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PredictableIntegrand_F000
-- name    : LevyStochCalc_Poisson_PredictableIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:41:50.243166+00:00
-- url     : https://prove2.me/theorems/648edc25-56cc-45c5-aa06-9a8715e1233e
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.PredictableIntegrand
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.PredictableIntegrand in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible marked integrands have predictable versions

An admissible marked integrand agrees almost everywhere with a predictable process; cutting that
process to the horizon keeps it predictable — the horizon strip is a countable union of windows
of finite mark measure — and makes it admissible, and the two compensated integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

/-- The horizon strip is predictable: it is the countable union of the windows of a σ-finite
exhaustion of the marks. -/
theorem measurableSet_markedPredictable_strip (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (ν : Measure E) [SigmaFinite ν] (T : ℝ) :
    MeasurableSet[markedPredictableSigma ℱ ν]
      ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))) := by
  have hrw : (Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      = ⋃ n : ℕ, ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν n)) := by
    ext p
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_iUnion, and_true]
    constructor
    · intro hs
      have hmem : p.2.2 ∈ ⋃ n, spanningSets ν n := by
        rw [iUnion_spanningSets ν]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
      exact ⟨n, hs, hn⟩
    · rintro ⟨n, hs, -⟩
      exact hs
  rw [hrw]
  exact MeasurableSet.iUnion fun n => measurableSet_univ_prod_window_self ℱ T
    (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n).ne
/-- Cutting a marked predictable process to a horizon keeps it predictable. -/
theorem markedPredictable_indicator_Ioc {ψ : Ω → ℝ → E → ℝ} (hψ : MarkedPredictable ℱ ν ψ)
    (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ ω s e) s := by
  have hset := measurableSet_markedPredictable_strip ℱ ν T
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ p.1 p.2.1 p.2.2) p.2.1)
      = ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))).indicator
        fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Ioc (0 : ℝ) T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod hp (Set.mem_univ _)))]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h => hp h.2.1]
  change Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ p.1 p.2.1 p.2.2) p.2.1
  rw [hrw]
  exact hψ.indicator hset
/-- The times outside a left-open horizon are null for the marked energy measure. -/
theorem ae_mem_Ioc_markedEnergyMeasure {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(markedEnergyMeasure P ν T), p.2.1 ∈ Set.Ioc (0 : ℝ) T := by
  have hnull : (markedEnergyMeasure P ν T)
      ((Set.univ : Set Ω) ×ˢ ((Set.Ioc (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set E))) = 0 := by
    have hset : ((Set.Ioc (0 : ℝ) T)ᶜ ∩ Set.Icc (0 : ℝ) T) = {(0 : ℝ)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ioc, Set.mem_Icc,
        Set.mem_singleton_iff, not_and, not_le]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases eq_or_lt_of_le h2 with h | h
        · exact h.symm
        · exact absurd h3 (not_le.mpr (h1 h))
      · rintro rfl
        exact ⟨fun h => absurd h (lt_irrefl 0), le_rfl, hT⟩
    rw [markedEnergyMeasure, Measure.prod_prod, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc.compl, hset]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod hp (Set.mem_univ _))
end LevyStochCalc.Poisson.Compensated


