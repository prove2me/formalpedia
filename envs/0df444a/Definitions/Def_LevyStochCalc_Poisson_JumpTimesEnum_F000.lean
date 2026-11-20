-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F000
-- name    : LevyStochCalc_Poisson_JumpTimesEnum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:33:12.491481+00:00
-- url     : https://prove2.me/theorems/a00fb521-9156-4362-ad72-33458d282b3f
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimesEnum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimesEnum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001
import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times as the atom times of a Poisson random measure

The counting process `arrivalCount N A` splits at a positive time into the mass strictly before
that time and the mass carried by the time itself, so on a window on which the restricted measure
is integer-valued a time in `(0, T]` carries mass in the mark set `A` exactly when it is one of
the arrival times `jumpTime N A i`. Such a time therefore lies among the times of any finite atom
set of the restricted measure. Every arrival time of positive index is strictly positive, the
arrival times of a time-simple measure strictly increase, and the chain of arrival times passes
any horizon at which the count is finite.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Singleton

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- The count over `(0, u]` splits into the count over `(0, u)` and the mass carried by `u`. -/
theorem arrivalCount_eq_add_count_singleton (hA : MeasurableSet A) {u : ℝ} (hu : 0 < u) (ω : Ω) :
    arrivalCount N A u ω
      = N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) + N.N ω (({u} : Set ℝ) ×ˢ A) := by
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) u ×ˢ A) (({u} : Set ℝ) ×ˢ A) := by
    rw [Set.disjoint_left]
    rintro ⟨x, e⟩ hmem hmem'
    have h1 : x < u := (Set.mem_prod.mp hmem).1.2
    have h2 : x = u := (Set.mem_prod.mp hmem').1
    linarith
  have hunion : Set.Ioc (0 : ℝ) u ×ˢ A
      = (Set.Ioo (0 : ℝ) u ×ˢ A) ∪ (({u} : Set ℝ) ×ˢ A) := by
    rw [← Set.union_prod]
    congr 1
    ext x
    simp only [Set.mem_Ioc, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le h2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, h2.le⟩
      · subst h
        exact ⟨hu, le_rfl⟩
  rw [arrivalCount, hunion, measure_union hdisj ((measurableSet_singleton u).prod hA)]
/-- The count at a time strictly below `u` together with the mass carried by `u` is at most the
count at `u`. -/
theorem arrivalCount_add_count_singleton_le (hA : MeasurableSet A) {t u : ℝ} (hu : 0 < u)
    (htu : t < u) (ω : Ω) :
    arrivalCount N A t ω + N.N ω (({u} : Set ℝ) ×ˢ A) ≤ arrivalCount N A u ω := by
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) t ×ˢ A) (({u} : Set ℝ) ×ˢ A) := by
    rw [Set.disjoint_left]
    rintro ⟨x, e⟩ hmem hmem'
    have h1 : x ≤ t := (Set.mem_prod.mp hmem).1.2
    have h2 : x = u := (Set.mem_prod.mp hmem').1
    linarith
  have hsub : (Set.Ioc (0 : ℝ) t ×ˢ A) ∪ (({u} : Set ℝ) ×ˢ A) ⊆ Set.Ioc (0 : ℝ) u ×ˢ A := by
    refine Set.union_subset (Set.prod_mono (Set.Ioc_subset_Ioc_right htu.le) le_rfl) ?_
    exact Set.prod_mono (Set.singleton_subset_iff.mpr ⟨hu, le_rfl⟩) le_rfl
  rw [arrivalCount, arrivalCount,
    ← measure_union hdisj ((measurableSet_singleton u).prod hA)]
  exact measure_mono hsub
/-- A bound valid for the counts at all times strictly below `u` bounds the mass on `(0, u)`. -/
theorem count_Ioo_le_of_forall_lt {u : ℝ} (hu : 0 < u) {ω : Ω}
    {M : ℝ≥0∞} (hM : ∀ t : ℝ, t < u → arrivalCount N A t ω ≤ M) :
    N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) ≤ M := by
  obtain ⟨r, hrmono, hrmem, hrtend⟩ := exists_seq_strictMono_tendsto' hu
  have hmono : Monotone fun n : ℕ => Set.Ioc (0 : ℝ) (r n) ×ˢ A := fun m n hmn =>
    Set.prod_mono (Set.Ioc_subset_Ioc_right (hrmono.monotone hmn)) le_rfl
  have hsub : Set.Ioo (0 : ℝ) u ×ˢ A ⊆ ⋃ n : ℕ, Set.Ioc (0 : ℝ) (r n) ×ˢ A := by
    rintro ⟨x, e⟩ hmem
    obtain ⟨hx, he⟩ := Set.mem_prod.mp hmem
    obtain ⟨n, hn⟩ := (hrtend.eventually_const_lt hx.2).exists
    exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hx.1, hn.le⟩, he⟩⟩
  calc N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A)
      ≤ N.N ω (⋃ n : ℕ, Set.Ioc (0 : ℝ) (r n) ×ˢ A) := measure_mono hsub
    _ = ⨆ n : ℕ, N.N ω (Set.Ioc (0 : ℝ) (r n) ×ˢ A) := hmono.measure_iUnion
    _ ≤ M := iSup_le fun n => hM (r n) (hrmem n).2
end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- On a window carrying integer mass the count at each earlier time is a natural number. -/
theorem exists_nat_arrivalCount (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {t : ℝ} (ht : t ≤ T) : ∃ n : ℕ, arrivalCount N A t ω = n := by
  obtain ⟨n, hn⟩ := hint (Set.Ioc (0 : ℝ) t ×ˢ A) (measurableSet_Ioc.prod hA)
  rw [Measure.restrict_apply (measurableSet_Ioc.prod hA),
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)] at hn
  exact ⟨n, hn⟩
/-- On a window carrying integer mass every time of the window carries a natural mass. -/
theorem exists_nat_count_singleton (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {u : ℝ} (hu : 0 < u) (huT : u ≤ T) : ∃ n : ℕ, N.N ω (({u} : Set ℝ) ×ˢ A) = n := by
  obtain ⟨n, hn⟩ := hint ((({u} : Set ℝ) ×ˢ A)) ((measurableSet_singleton u).prod hA)
  rw [Measure.restrict_apply ((measurableSet_singleton u).prod hA),
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hu, huT⟩)) le_rfl)] at hn
  exact ⟨n, hn⟩
/-- On a window carrying integer mass the count at each earlier time is finite. -/
theorem arrivalCount_ne_top_of_isIntegerValued (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {t : ℝ} (ht : t ≤ T) : arrivalCount N A t ω ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_arrivalCount N A hA hint ht
  rw [hn]
  exact ENNReal.natCast_ne_top n
end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Arrival times of positive index are strictly positive. -/
theorem coe_zero_lt_jumpTime (hA : MeasurableSet A) {i : ℕ} (hi : i ≠ 0) {ω : Ω}
    (hfin : arrivalCount N A 1 ω ≠ ⊤) : ((0 : ℝ) : WithTop ℝ) < jumpTime N A i ω := by
  refine lt_of_le_of_ne (coe_zero_le_jumpTime N A i ω) fun hcon => ?_
  have hfin' : arrivalCount N A ((0 : ℝ) + 1) ω ≠ ⊤ := by simpa using hfin
  have h := (_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA (le_refl (0 : ℝ)) hfin').mp (le_of_eq hcon.symm)
  rw [arrivalCount_of_nonpos N A (le_refl (0 : ℝ)) ω] at h
  exact hi (by exact_mod_cast le_antisymm h zero_le)
end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Before the `i`-th arrival time of a window carrying integer mass the count is at most
`i - 1`. -/
theorem arrivalCount_le_of_jumpTime_eq (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    {i : ℕ} {u : ℝ} (hiu : jumpTime N A i ω = (u : WithTop ℝ)) (huT : u ≤ T) {t : ℝ}
    (htu : t < u) : arrivalCount N A t ω ≤ ((i - 1 : ℕ) : ℝ≥0∞) := by
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [arrivalCount_of_nonpos N A ht0 ω]
    exact zero_le
  · by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := exists_nat_arrivalCount N A hA hint (show t ≤ T + 1 by linarith)
    rw [hn] at hcon
    have hin : i ≤ n := by
      have hlt : i - 1 < n := by exact_mod_cast hcon
      omega
    have hge : (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by
      rw [hn]
      exact_mod_cast hin
    have hlt : jumpTime N A i ω < (u : WithTop ℝ) :=
      (_root_.Prove2MeSourceProof.h_1849eb0e6619cf2c91089130 N A i u ω).mpr ⟨t, ht0.le, htu, hge⟩
    rw [hiu] at hlt
    exact lt_irrefl _ hlt
/-- The mass strictly before the `i`-th arrival time of a window carrying integer mass is at most
`i - 1`. -/
theorem count_Ioo_le_of_jumpTime_eq (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    {i : ℕ} {u : ℝ} (hu : 0 < u) (hiu : jumpTime N A i ω = (u : WithTop ℝ)) (huT : u ≤ T) :
    N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) ≤ ((i - 1 : ℕ) : ℝ≥0∞) :=
  count_Ioo_le_of_forall_lt N A hu fun _ htu =>
    arrivalCount_le_of_jumpTime_eq N A hA hint hiu huT htu
end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Chain

section AtomFinset

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomFinset

section AtomPoint

variable [MeasurableSingletonClass E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomPoint

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

variable [MeasurableSingletonClass E]

end AlmostEverywhere

end LevyStochCalc.Poisson


