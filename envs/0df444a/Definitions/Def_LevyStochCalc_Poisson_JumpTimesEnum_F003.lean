-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F003
-- name    : LevyStochCalc_Poisson_JumpTimesEnum_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:48:12.382199+00:00
-- url     : https://prove2.me/theorems/5ff4b90c-813c-45f3-bdb6-7f85eaf4a35c
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
import Definitions.Def_SourceProof_fd1036cdbd6026022399ce5b

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

end AtomPoint

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Almost surely the arrival times in `(0, T]` are exactly the times of `(0, T]` carrying mass in
the mark set. -/
theorem ae_setOf_jumpTime_eq_setOf_count_singleton_ne_zero (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (T : ℝ) :
    ∀ᵐ ω ∂P, {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}
      = {u : ℝ | (0 < u ∧ u ≤ T) ∧ N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0} := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν (T + 1))] with ω hint
  exact _root_.Prove2MeSourceProof.h_fd1036cdbd6026022399ce5b N A hA hint
variable [MeasurableSingletonClass E]

end AlmostEverywhere

end LevyStochCalc.Poisson


