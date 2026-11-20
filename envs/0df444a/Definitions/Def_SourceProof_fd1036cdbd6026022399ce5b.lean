-- Prove2me | Definitions.Def_SourceProof_fd1036cdbd6026022399ce5b
-- name    : SourceProof_fd1036cdbd6026022399ce5b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:47:46.514893+00:00
-- url     : https://prove2.me/theorems/7fdd65b8-90db-460f-8666-8309e488be48
-- title:
--   LevyStochCalc source module: SourceProof_fd1036cdbd6026022399ce5b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.setOf_jumpTime_eq_setOf_count_singleton_ne_zero` comes from the `LevyStochCalc.Poisson.JumpTimesEnum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F000

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


theorem _root_.Prove2MeSourceProof.h_fd1036cdbd6026022399ce5b (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A))) :
    {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}
      = {u : ℝ | (0 < u ∧ u ≤ T) ∧ N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0} := by
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hiu, hu0, huT⟩
    refine ⟨⟨hu0, huT⟩, fun hzero => ?_⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [LevyStochCalc.Poisson.jumpTime_zero] at hiu
      have h0 : (0 : ℝ) = u := by exact_mod_cast hiu
      linarith
    have hfinu : LevyStochCalc.Poisson.arrivalCount N A (u + 1) ω ≠ ⊤ :=
      LevyStochCalc.Poisson.arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hle : (i : ℝ≥0∞) ≤ LevyStochCalc.Poisson.arrivalCount N A u ω :=
      (_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA hu0.le hfinu).mp (le_of_eq hiu)
    have hIoo := LevyStochCalc.Poisson.count_Ioo_le_of_jumpTime_eq N A hA hint hu0 hiu huT
    have hdec := LevyStochCalc.Poisson.arrivalCount_eq_add_count_singleton N A hA hu0 ω
    rw [hzero, add_zero] at hdec
    have hcontr : (i : ℝ≥0∞) ≤ ((i - 1 : ℕ) : ℝ≥0∞) := hle.trans (hdec.trans_le hIoo)
    have hnat : i ≤ i - 1 := by exact_mod_cast hcontr
    omega
  · rintro ⟨⟨hu0, huT⟩, hne⟩
    obtain ⟨n, hn⟩ := LevyStochCalc.Poisson.exists_nat_arrivalCount N A hA hint (show u ≤ T + 1 by linarith)
    have hfinu : LevyStochCalc.Poisson.arrivalCount N A (u + 1) ω ≠ ⊤ :=
      LevyStochCalc.Poisson.arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    refine ⟨n, le_antisymm ((_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA hu0.le hfinu).mpr (le_of_eq hn.symm)) ?_,
      hu0, huT⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht0, htu, hcount⟩ := (_root_.Prove2MeSourceProof.h_1849eb0e6619cf2c91089130 N A n u ω).mp hcon
    have hct : LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤ :=
      LevyStochCalc.Poisson.arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hstrict : LevyStochCalc.Poisson.arrivalCount N A t ω < LevyStochCalc.Poisson.arrivalCount N A u ω :=
      lt_of_lt_of_le (ENNReal.lt_add_right hct hne)
        (LevyStochCalc.Poisson.arrivalCount_add_count_singleton_le N A hA hu0 htu ω)
    rw [hn] at hstrict
    exact absurd hcount (not_le.mpr hstrict)
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


