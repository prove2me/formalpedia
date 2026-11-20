-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F004
-- name    : LevyStochCalc_Poisson_JumpTimesEnum_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:49:21.458195+00:00
-- url     : https://prove2.me/theorems/c063f5d0-c303-4a25-b041-7f601ee5d7eb
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimesEnum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimesEnum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F001
import Definitions.Def_SourceProof_6a21e32323164b04c65b4566
import Definitions.Def_SourceProof_935684fe1e6aea9a3a83dadb
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

omit [MeasurableSpace.CountablyGenerated E] in
/-- Almost surely the chain of arrival times starts at the origin and passes the horizon `T`. -/
theorem ae_jumpTime_chain (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, jumpTime N A 0 ω ≤ ((0 : ℝ) : WithTop ℝ) ∧
      ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω := by
  filter_upwards [count_Ioc_ne_top N hA hAν T] with ω hω
  exact jumpTime_chain_of_ne_top N A hω
variable [MeasurableSingletonClass E]

/-- **The arrival times enumerate the atoms of the window.** Almost surely the window carries a
finite set of time–mark points computing every integral over it whose times are exactly the
arrival times in `(0, T]`. -/
theorem ae_exists_finset_jumpTimes_eq (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (∀ g : ℝ × E → ℝ≥0∞,
        ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
          = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p) ∧
        (jumpTimes s : Set ℝ)
          = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} := by
  classical
  filter_upwards [ae_exists_finset_integral_eq_sum_Ioc N hA hAν T,
    _root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N (measurableSet_Ioc.prod hA)
      (referenceIntensity_Ioc_prod_ne_top hAν (T + 1))] with ω hω hint
  obtain ⟨s, hs, -, -⟩ := hω
  refine ⟨s.filter fun p => ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0,
    fun g => ?_, ?_⟩
  · rw [hs g]
    refine (Finset.sum_filter_of_ne
      (p := fun q => ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {q} ≠ 0) ?_).symm
    intro x _ hx hzero
    exact hx (by rw [hzero, zero_mul])
  · rw [_root_.Prove2MeSourceProof.h_fd1036cdbd6026022399ce5b N A hA hint]
    ext x
    constructor
    · intro hx
      obtain ⟨p, hps, hpx⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      rw [← hpx]
      exact _root_.Prove2MeSourceProof.h_6a21e32323164b04c65b4566 N A (Finset.mem_filter.mp hps).2
    · rintro ⟨⟨hx0, hxT⟩, hne⟩
      obtain ⟨p, hps, hpm, hpx⟩ :=
        _root_.Prove2MeSourceProof.h_935684fe1e6aea9a3a83dadb N A hA hs hx0 hxT hne
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hps, hpm⟩, hpx⟩)
end AlmostEverywhere

end LevyStochCalc.Poisson


