-- Prove2me | Definitions.Def_SourceProof_935684fe1e6aea9a3a83dadb
-- name    : SourceProof_935684fe1e6aea9a3a83dadb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:23:12.734578+00:00
-- url     : https://prove2.me/theorems/34fe4d30-8b3b-4c42-87f0-4b45ee467f8c
-- title:
--   LevyStochCalc source module: SourceProof_935684fe1e6aea9a3a83dadb
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exists_mem_of_count_singleton_ne_zero` comes from the `LevyStochCalc.Poisson.JumpTimesEnum` module. The staged Lean declaration includes its source proof and dependency references.
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

end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Chain

section AtomFinset

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)


theorem _root_.Prove2MeSourceProof.h_935684fe1e6aea9a3a83dadb (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    {s : Finset (ℝ × E)}
    (hs : ∀ g : ℝ × E → ℝ≥0∞,
      ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p)
    {u : ℝ} (hu0 : 0 < u) (huT : u ≤ T) (hne : N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0) :
    ∃ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0 ∧ p.1 = u := by
  classical
  have hmeas : MeasurableSet ((({u} : Set ℝ) ×ˢ A : Set (ℝ × E))) :=
    (measurableSet_singleton u).prod hA
  have hkey := hs ((({u} : Set ℝ) ×ˢ A).indicator 1)
  rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas,
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hu0, huT⟩))
        le_rfl)] at hkey
  have hsum : (∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p}
      * (({u} : Set ℝ) ×ˢ A).indicator 1 p) ≠ 0 := by
    rw [← hkey]
    exact hne
  obtain ⟨p, hps, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hpmem : p ∈ ((({u} : Set ℝ) ×ˢ A) : Set (ℝ × E)) := by
    by_contra hc
    exact hp0 (by rw [Set.indicator_of_notMem hc, mul_zero])
  refine ⟨p, hps, fun hzero => hp0 ?_, (Set.mem_prod.mp hpmem).1⟩
  rw [hzero, zero_mul]
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


