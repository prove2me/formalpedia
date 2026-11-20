-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F002
-- name    : LevyStochCalc_Poisson_JumpTimesEnum_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:23:50.818927+00:00
-- url     : https://prove2.me/theorems/76ce28c4-8730-4299-8c5a-00fcd4e982f7
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
import Definitions.Def_SourceProof_935684fe1e6aea9a3a83dadb

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

/-- A time of the window carrying mass in the mark set is one of the times of an atom finset of
the restricted measure. -/
theorem mem_jumpTimes_of_count_singleton_ne_zero (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    {s : Finset (ℝ × E)}
    (hs : ∀ g : ℝ × E → ℝ≥0∞,
      ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p)
    {u : ℝ} (hu0 : 0 < u) (huT : u ≤ T) (hne : N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0) :
    u ∈ jumpTimes s := by
  obtain ⟨p, hps, -, hpu⟩ := _root_.Prove2MeSourceProof.h_935684fe1e6aea9a3a83dadb N A hA hs hu0 huT hne
  exact Finset.mem_image.mpr ⟨p, hps, hpu⟩
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


