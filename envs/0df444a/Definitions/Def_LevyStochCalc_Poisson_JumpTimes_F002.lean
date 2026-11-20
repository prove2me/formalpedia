-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002
-- name    : LevyStochCalc_Poisson_JumpTimes_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:30:25.290228+00:00
-- url     : https://prove2.me/theorems/663f7316-6d9f-4df5-b245-f90dd184507e
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimes
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimes. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000
import Definitions.Def_SourceProof_89951611d96c791ecb431bce

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times of a Poisson random measure on a mark set

`arrivalCount N A t ω` is the number of points of a Poisson random measure `N` whose time lies in
`(0, t]` and whose mark lies in `A`. It is monotone in the time, measurable for every filtration
for which `N` is a Poisson random measure, and right-continuous at every time from which it stays
finite. The `i`-th arrival time `jumpTime N A i` is the first nonnegative time at which the count
reaches `i`, and `⊤` when the count never reaches `i`; it is a stopping time for the
right-continuous filtration `ℱ₊`, and for `ℱ` itself when the counting process is everywhere
finite. Over a window on which the count is finite only finitely many arrival times occur, and
they carry a strictly monotone enumeration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section MarkCount

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end MarkCount

section JumpTime

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- Only finitely many arrival times fall inside a window on which the count is finite. -/
theorem finite_setOf_jumpTime_le (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    {i : ℕ | jumpTime N A i ω ≤ (T : WithTop ℝ)}.Finite := by
  have hcT : arrivalCount N A T ω ≠ ⊤ := by
    intro hcon
    exact hfin (top_le_iff.mp (hcon ▸ arrivalCount_mono N A ω (by linarith : T ≤ T + 1)))
  refine Set.Finite.subset (Set.finite_Iic ⌈(arrivalCount N A T ω).toReal⌉₊) fun i hi => ?_
  have hle : (i : ℝ≥0∞) ≤ arrivalCount N A T ω := (_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA hT hfin).mp hi
  have hre : (i : ℝ) ≤ (arrivalCount N A T ω).toReal := by
    simpa using ENNReal.toReal_mono hcT hle
  exact Nat.cast_le.mp (hre.trans (Nat.le_ceil _))
/-- Almost surely only finitely many arrival times fall inside a window, for a mark set of finite
intensity. -/
theorem ae_finite_setOf_jumpTime_le (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, {i : ℕ | jumpTime N A i ω ≤ (T : WithTop ℝ)}.Finite := by
  filter_upwards [count_Ioc_ne_top N hA hAν (T + 1)] with ω hω
  exact finite_setOf_jumpTime_le N A hA hT hω
end Finiteness

end LevyStochCalc.Poisson


