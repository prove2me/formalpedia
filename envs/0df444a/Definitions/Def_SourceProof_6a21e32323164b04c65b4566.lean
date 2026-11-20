-- Prove2me | Definitions.Def_SourceProof_6a21e32323164b04c65b4566
-- name    : SourceProof_6a21e32323164b04c65b4566
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:22:34.628414+00:00
-- url     : https://prove2.me/theorems/9d2c6d25-031c-49b6-b2f8-aaa8713e1fa7
-- title:
--   LevyStochCalc source module: SourceProof_6a21e32323164b04c65b4566
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.count_singleton_ne_zero_of_restrict_ne_zero` comes from the `LevyStochCalc.Poisson.JumpTimesEnum` module. The staged Lean declaration includes its source proof and dependency references.
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

end AtomFinset

section AtomPoint

variable [MeasurableSingletonClass E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)


theorem _root_.Prove2MeSourceProof.h_6a21e32323164b04c65b4566 {T : ℝ} {ω : Ω} {p : ℝ × E}
    (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0) :
    (0 < p.1 ∧ p.1 ≤ T) ∧ N.N ω (({p.1} : Set ℝ) ×ˢ A) ≠ 0 := by
  have hpR : p ∈ Set.Ioc (0 : ℝ) T ×ˢ A := by
    by_contra hc
    exact hp (by rw [Measure.restrict_apply (measurableSet_singleton p),
      Set.singleton_inter_eq_empty.mpr hc, measure_empty])
  have hsub : ({p} : Set (ℝ × E)) ⊆ (({p.1} : Set ℝ) ×ˢ A) :=
    Set.singleton_subset_iff.mpr ⟨rfl, (Set.mem_prod.mp hpR).2⟩
  refine ⟨Set.mem_Ioc.mp (Set.mem_prod.mp hpR).1, fun hzero => hp (le_antisymm ?_ zero_le)⟩
  calc ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p}
      ≤ N.N ω ({p} : Set (ℝ × E)) := Measure.restrict_apply_le _ _
    _ ≤ N.N ω ((({p.1} : Set ℝ) ×ˢ A)) := measure_mono hsub
    _ = 0 := hzero
end AtomPoint

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

variable [MeasurableSingletonClass E]

end AlmostEverywhere

end LevyStochCalc.Poisson


