-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
-- name    : LevyStochCalc_Poisson_FiniteActivity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:17:07.090214+00:00
-- url     : https://prove2.me/theorems/8062dced-6cd4-4a44-aea7-4ccd7d5336b7
-- title:
--   Source declarations: LevyStochCalc.Poisson.FiniteActivity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.FiniteActivity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite activity on a mark set of finite intensity

Over a bounded time window the reference intensity of a mark set of finite intensity is finite,
so the count of the Poisson random measure there is almost surely a natural number, hence finite.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The reference intensity of a time window times a mark set. -/
theorem referenceIntensity_Ioc_prod (A : Set E) (T : ℝ) :
    referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) = ENNReal.ofReal T * ν A := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  congr 1
  have hset : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => h.1.le
  rw [hset, Real.volume_Ioc, sub_zero]
/-- A time window times a mark set of finite intensity has finite reference intensity. -/
theorem referenceIntensity_Ioc_prod_ne_top {A : Set E} (hAν : ν A ≠ ⊤) (T : ℝ) :
    referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_Ioc_prod A T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAν
/-- **Finite activity.** Over a bounded window, the count on a mark set of finite intensity is
almost surely a natural number, hence finite. -/
theorem exists_nat_count_Ioc (N : PoissonRandomMeasure P ν) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω (Set.Ioc (0 : ℝ) T ×ˢ A) = n :=
  N.integer_valued (measurableSet_Ioc.prod hA) (referenceIntensity_Ioc_prod_ne_top hAν T)
/-- The count on a mark set of finite intensity over a bounded window is almost surely finite. -/
theorem count_Ioc_ne_top (N : PoissonRandomMeasure P ν) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, N.N ω (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ := by
  filter_upwards [exists_nat_count_Ioc N hA hAν T] with ω hω
  obtain ⟨n, hn⟩ := hω
  rw [hn]
  exact ENNReal.natCast_ne_top n
end LevyStochCalc.Poisson


