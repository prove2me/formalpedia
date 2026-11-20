-- Prove2me | Definitions.Def_SourceProof_3b4c8aaeb3983333d32ff10f
-- name    : SourceProof_3b4c8aaeb3983333d32ff10f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:54:53.861513+00:00
-- url     : https://prove2.me/theorems/1be64d1c-2026-465e-a7a9-703065449e7b
-- title:
--   LevyStochCalc source module: SourceProof_3b4c8aaeb3983333d32ff10f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ` comes from the `LevyStochCalc.Poisson.JumpTimesEnum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F001
import Definitions.Def_SourceProof_07135226a3b6eb1d82b734e1

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


theorem _root_.Prove2MeSourceProof.h_3b4c8aaeb3983333d32ff10f (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, jumpTime N A (i + 1) ω ≤ (T : WithTop ℝ) →
      jumpTime N A i ω < jumpTime N A (i + 1) ω := by
  have hB : MeasurableSet (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν (T + 1)
  filter_upwards [_root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hB hfin,
    _root_.Prove2MeSourceProof.h_07135226a3b6eb1d82b734e1 N hB hfin] with ω hint hsimple i hi
  refine LevyStochCalc.Poisson.jumpTime_lt_jumpTime_succ N A hA hint (fun x hx0 hxT => ?_) hi
  have hset : Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({x} : Set ℝ) ×ˢ (Set.univ : Set E)
      = ({x} : Set ℝ) ×ˢ A := by
    rw [Set.prod_inter_prod, Set.inter_univ,
      Set.inter_eq_self_of_subset_right
        (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hx0, by linarith⟩))]
  exact hset ▸ hsimple x
variable [MeasurableSingletonClass E]

end AlmostEverywhere

end LevyStochCalc.Poisson


