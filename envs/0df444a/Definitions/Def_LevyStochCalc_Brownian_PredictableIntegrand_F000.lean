-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PredictableIntegrand_F000
-- name    : LevyStochCalc_Brownian_PredictableIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:15.968583+00:00
-- url     : https://prove2.me/theorems/719cc1c2-9e13-4254-92c3-10c51c918330
-- title:
--   Source declarations: LevyStochCalc.Brownian.PredictableIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PredictableIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F001
import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible integrands have predictable versions

An admissible integrand agrees almost everywhere with a predictable process; cutting that process
to the horizon keeps it predictable and makes it admissible, and the two integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

/-- The predictable σ-algebra is coarser than the product σ-algebra. -/
theorem predictableSigma_le (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    predictableSigma ℱ ≤ (inferInstance : MeasurableSpace (ℝ × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨r, A, hA, rfl⟩)
  · exact measurableSet_Iic.prod (ℱ.le 0 _ hA)
  · exact measurableSet_Ioi.prod (ℱ.le r _ hA)
/-- A predictable process is jointly measurable. -/
theorem measurable_uncurry_of_predictable {K : Ω → ℝ → ℝ} (hK : Predictable ℱ K) :
    Measurable (Function.uncurry K) :=
  ((hK.mono (predictableSigma_le ℱ)).measurable).comp measurable_swap
/-- Cutting a predictable process to a horizon keeps it predictable. -/
theorem predictable_indicator_Ioc {K : Ω → ℝ → ℝ} (hK : Predictable ℱ K) {T : ℝ} (hT : 0 ≤ T) :
    Predictable ℱ fun ω s => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K ω s) s := by
  have hset : MeasurableSet[predictableSigma ℱ] (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set Ω)) :=
    _root_.Prove2MeSourceProof.h_4ecfd1aa58bb4ad860581e64 hT MeasurableSet.univ
  have hrw : (fun p : ℝ × Ω => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K p.2 p.1) p.1)
      = (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set Ω)).indicator fun p : ℝ × Ω => K p.2 p.1 := by
    funext p
    by_cases hp : p.1 ∈ Set.Ioc (0 : ℝ) T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mk_mem_prod hp (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h => hp h.1]
  change StronglyMeasurable[predictableSigma ℱ]
    fun p : ℝ × Ω => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K p.2 p.1) p.1
  rw [hrw]
  exact hK.indicator hset
/-- The times outside a left-open horizon are null for the energy measure. -/
theorem ae_mem_Ioc_energyMeasure {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(energyMeasure P T), p.2 ∈ Set.Ioc (0 : ℝ) T := by
  have hmeas : MeasurableSet ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ) :=
    MeasurableSet.univ.prod measurableSet_Ioc.compl
  have hnull : (energyMeasure P T) ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ) = 0 := by
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
    rw [energyMeasure, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl, hset]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact Set.mk_mem_prod (Set.mem_univ _) hp
end LevyStochCalc.Brownian.Ito


