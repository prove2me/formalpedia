-- Prove2me | Definitions.Def_SourceProof_89951611d96c791ecb431bce
-- name    : SourceProof_89951611d96c791ecb431bce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:29:53.272614+00:00
-- url     : https://prove2.me/theorems/73ef07a7-fc3b-4715-b7a8-194f5555f475
-- title:
--   LevyStochCalc source module: SourceProof_89951611d96c791ecb431bce
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.jumpTime_le_iff` comes from the `LevyStochCalc.Poisson.JumpTimes` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000

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


theorem _root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce (hA : MeasurableSet A) {i : ℕ} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hfin : arrivalCount N A (t + 1) ω ≠ ⊤) :
    jumpTime N A i ω ≤ (t : WithTop ℝ) ↔ (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by
  constructor
  · intro hle
    rw [LevyStochCalc.Poisson.jumpTime] at hle
    split_ifs at hle with hne
    · have hst : sInf (LevyStochCalc.Poisson.jumpTimeSet N A i ω) ≤ t := by exact_mod_cast hle
      rw [← LevyStochCalc.Poisson.iInf_arrivalCount_gt N A hA (lt_add_one t) hfin]
      refine le_iInf₂ fun s hs => ?_
      obtain ⟨w, hw, hws⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt hst hs)
      exact hw.2.trans (LevyStochCalc.Poisson.arrivalCount_mono N A ω hws.le)
    · exact absurd hle (by simp)
  · intro hcount
    rw [LevyStochCalc.Poisson.jumpTime, if_pos ⟨t, ht, hcount⟩]
    exact_mod_cast csInf_le (LevyStochCalc.Poisson.bddBelow_jumpTimeSet N A i ω) ⟨ht, hcount⟩
end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end Finiteness

end LevyStochCalc.Poisson


