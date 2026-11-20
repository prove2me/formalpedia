-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimesComplete_F000
-- name    : LevyStochCalc_Poisson_JumpTimesComplete_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:26:57.826949+00:00
-- url     : https://prove2.me/theorems/d0f06e2b-2cb7-4639-8b6f-7c3833f62d19
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimesComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimesComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001
import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002
import Definitions.Def_SourceProof_fd667ca169170e4cdeb4bb71

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times as stopping times for a filtration containing the null sets

For a filtration whose time-zero σ-algebra contains the `P`-null sets, the arrival times
`jumpTime N A i` of a Poisson random measure `N` in a mark set `A` of finite intensity are
stopping times for the filtration itself: the counting process is almost surely finite at every
time, and the exceptional set is absorbed by the null sets of the time-zero σ-algebra. This
avoids both the pathwise finiteness hypothesis of `isStoppingTime_jumpTime` and the passage to
the right-continuous filtration in `isStoppingTime_jumpTime_rightCont`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- The arrival times of `N` in a mark set of finite intensity form an increasing chain of
stopping times for a filtration whose time-zero σ-algebra contains the `P`-null sets, starting
at the origin. -/
theorem isStoppingTime_jumpTime_chain_of_complete {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    (∀ k : ℕ, IsStoppingTime ℱ (jumpTime N A k))
      ∧ (∀ (k : ℕ) (ω : Ω), jumpTime N A k ω ≤ jumpTime N A (k + 1) ω)
      ∧ (∀ ω : Ω, jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ)) :=
  ⟨fun k => _root_.Prove2MeSourceProof.h_fd667ca169170e4cdeb4bb71 N A hℱ hA hAν hnull k,
    fun k ω => jumpTime_mono N A (Nat.le_succ k) ω, jumpTime_zero N A⟩
end LevyStochCalc.Poisson


