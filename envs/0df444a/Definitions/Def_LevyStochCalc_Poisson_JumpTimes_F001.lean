-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001
-- name    : LevyStochCalc_Poisson_JumpTimes_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:28:45.891583+00:00
-- url     : https://prove2.me/theorems/cbd2532b-18e2-4866-89c4-2251bf76c855
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimes
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimes. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000
import Definitions.Def_SourceProof_1849eb0e6619cf2c91089130
import Definitions.Def_SourceProof_cbb0fd7558e885b374c4446f

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

/-- The `i`-th arrival time is strictly below `t` exactly when the count reaches `i` at some
nonnegative rational time strictly below `t`. -/
theorem jumpTime_lt_iff_rat (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω < (t : WithTop ℝ)
      ↔ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A (q : ℝ) ω := by
  rw [_root_.Prove2MeSourceProof.h_1849eb0e6619cf2c91089130]
  constructor
  · rintro ⟨s, hs0, hst, hcount⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hst
    exact ⟨q, hs0.trans hq1.le, hq2, hcount.trans (arrivalCount_mono N A ω hq1.le)⟩
  · rintro ⟨q, h0, h1, h2⟩
    exact ⟨(q : ℝ), h0, h1, h2⟩
/-- The event that the `i`-th arrival time is strictly below `t` is known at time `t`. -/
theorem measurableSet_jumpTime_lt {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (i : ℕ) (t : ℝ) :
    MeasurableSet[ℱ t] {ω | jumpTime N A i ω < (t : WithTop ℝ)} := by
  have hset : {ω | jumpTime N A i ω < (t : WithTop ℝ)}
      = ⋃ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < t},
          {ω | (i : ℝ≥0∞) ≤ arrivalCount N A ((q : ℚ) : ℝ) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists]
    rw [jumpTime_lt_iff_rat]
    exact ⟨fun ⟨q, h0, h1, h2⟩ => ⟨q, ⟨h0, h1⟩, h2⟩, fun ⟨q, ⟨h0, h1⟩, h2⟩ => ⟨q, h0, h1, h2⟩⟩
  have hq : ∀ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < t},
      MeasurableSet[ℱ t] {ω | (i : ℝ≥0∞) ≤ arrivalCount N A ((q : ℚ) : ℝ) ω} := fun q =>
    ℱ.mono q.2.2.le _ (measurable_arrivalCount N A hℱ hA ((q : ℚ) : ℝ) measurableSet_Ici)
  rw [hset]
  exact MeasurableSet.iUnion (m := ℱ t) hq
/-- **The arrival times are stopping times.** For a Poisson random measure adapted to `ℱ`, the
`i`-th arrival time in a measurable mark set is a stopping time for the right-continuous
filtration `ℱ₊`. -/
theorem isStoppingTime_jumpTime_rightCont {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (i : ℕ) :
    IsStoppingTime ℱ.rightCont (jumpTime N A i) :=
  MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun t => ℱ.le_rightCont t _ (measurableSet_jumpTime_lt N A hℱ hA i t)
end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end Finiteness

end LevyStochCalc.Poisson


