-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F001
-- name    : LevyStochCalc_Poisson_JumpTimesEnum_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:25:29.6882+00:00
-- url     : https://prove2.me/theorems/a4b5b819-9ea8-423f-b7e8-35d84f07cead
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimesEnum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimesEnum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F000
import Definitions.Def_SourceProof_e47911331b088187d1ff7470

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

end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- **The arrival times of a time-simple measure strictly increase.** -/
theorem jumpTime_lt_jumpTime_succ (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ, 0 < u → u ≤ T → N.N ω (({u} : Set ℝ) ×ˢ A) ≤ 1) {i : ℕ}
    (hi : jumpTime N A (i + 1) ω ≤ (T : WithTop ℝ)) :
    jumpTime N A i ω < jumpTime N A (i + 1) ω := by
  obtain ⟨u, hu⟩ :=
    WithTop.ne_top_iff_exists.mp (lt_of_le_of_lt hi (WithTop.coe_lt_top T)).ne
  have huT : u ≤ T := by
    have hcast : ((u : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := by rw [hu]; exact hi
    exact_mod_cast hcast
  have hT0 : 0 ≤ T := by
    have hcast : ((0 : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) :=
      (coe_zero_le_jumpTime N A (i + 1) ω).trans hi
    exact_mod_cast hcast
  have hfin1 : arrivalCount N A 1 ω ≠ ⊤ :=
    arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
  have hu0 : 0 < u := by
    have hpos := coe_zero_lt_jumpTime N A hA (Nat.succ_ne_zero i) hfin1
    rw [← hu] at hpos
    exact_mod_cast hpos
  refine lt_of_le_of_ne (jumpTime_mono N A (Nat.le_succ i) ω) fun heq => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [jumpTime_zero, ← hu] at heq
    have h0 : (0 : ℝ) = u := by exact_mod_cast heq
    linarith
  · have hiu : jumpTime N A i ω = ((u : ℝ) : WithTop ℝ) := by rw [heq, ← hu]
    have hIoo := count_Ioo_le_of_jumpTime_eq N A hA hint hu0 hiu huT
    have hdec := arrivalCount_eq_add_count_singleton N A hA hu0 ω
    have hsum : ((i - 1 : ℕ) : ℝ≥0∞) + 1 = (i : ℝ≥0∞) := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp
    have hcu : arrivalCount N A u ω ≤ (i : ℝ≥0∞) := by
      rw [hdec]
      calc N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) + N.N ω (({u} : Set ℝ) ×ˢ A)
          ≤ ((i - 1 : ℕ) : ℝ≥0∞) + 1 := add_le_add hIoo (hsimple u hu0 huT)
        _ = (i : ℝ≥0∞) := hsum
    have hfinu : arrivalCount N A (u + 1) ω ≠ ⊤ :=
      arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hge : ((i + 1 : ℕ) : ℝ≥0∞) ≤ arrivalCount N A u ω :=
      (_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA hu0.le hfinu).mp (le_of_eq hu.symm)
    have hnat : i + 1 ≤ i := by exact_mod_cast hge.trans hcu
    omega
end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- **The chain of arrival times passes any horizon of finite count.** -/
theorem exists_coe_le_jumpTime {T : ℝ} {ω : Ω} (hfin : arrivalCount N A T ω ≠ ⊤) :
    ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω := by
  refine ⟨⌈(arrivalCount N A T ω).toReal⌉₊ + 1, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs0, hsT, hle⟩ :=
    (_root_.Prove2MeSourceProof.h_1849eb0e6619cf2c91089130 N A (⌈(arrivalCount N A T ω).toReal⌉₊ + 1) T ω).mp hcon
  have h1 : ((⌈(arrivalCount N A T ω).toReal⌉₊ + 1 : ℕ) : ℝ≥0∞) ≤ arrivalCount N A T ω :=
    hle.trans (arrivalCount_mono N A ω hsT.le)
  have h2 : ((⌈(arrivalCount N A T ω).toReal⌉₊ + 1 : ℕ) : ℝ) ≤ (arrivalCount N A T ω).toReal := by
    have h2' := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_natCast] at h2'
  have h3 := Nat.le_ceil (arrivalCount N A T ω).toReal
  push_cast at h2
  linarith
/-- The chain of arrival times starts at the origin and passes any horizon of finite count. -/
theorem jumpTime_chain_of_ne_top {T : ℝ} {ω : Ω} (hfin : arrivalCount N A T ω ≠ ⊤) :
    jumpTime N A 0 ω ≤ ((0 : ℝ) : WithTop ℝ) ∧
      ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω :=
  ⟨le_of_eq (jumpTime_zero N A ω), exists_coe_le_jumpTime N A hfin⟩
/-- Only finitely many arrival times fall in the window `(0, T]` when the count is finite. -/
theorem finite_setOf_arrivalTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}.Finite := by
  obtain ⟨k, e, -, hrange⟩ := _root_.Prove2MeSourceProof.h_e47911331b088187d1ff7470 N A hA hT hfin
  refine Set.Finite.subset (hrange ▸ Set.finite_range e) ?_
  rintro u ⟨i, hiu, -, huT⟩
  exact ⟨i, hiu, huT⟩
/-- The arrival times in the window `(0, T]` carry a strictly monotone enumeration. -/
theorem exists_strictMono_enum_arrivalTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧
      Set.range e = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} := by
  obtain ⟨k, e, he, hrange⟩ :=
    exists_strictMono_enum (finite_setOf_arrivalTime N A hA hT hfin).toFinset
  exact ⟨k, e, he, by rwa [Set.Finite.coe_toFinset] at hrange⟩
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


