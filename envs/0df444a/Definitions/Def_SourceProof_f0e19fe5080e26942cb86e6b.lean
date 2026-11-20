-- Prove2me | Definitions.Def_SourceProof_f0e19fe5080e26942cb86e6b
-- name    : SourceProof_f0e19fe5080e26942cb86e6b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:50:40.727124+00:00
-- url     : https://prove2.me/theorems/251e1bab-b8f0-4304-9cde-a568d791e8fe
-- title:
--   LevyStochCalc source module: SourceProof_f0e19fe5080e26942cb86e6b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.isStoppingTime_jumpTime` comes from the `LevyStochCalc.Poisson.JumpTimes` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_f0e19fe5080e26942cb86e6b {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), arrivalCount N A t ω ≠ ⊤) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h0 : ((0 : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ) :=
        (LevyStochCalc.Poisson.coe_zero_le_jumpTime N A i ω).trans hle
      exact absurd (by exact_mod_cast h0 : (0 : ℝ) ≤ t) (not_le.mpr ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)}
        = {ω | (i : ℝ≥0∞) ≤ LevyStochCalc.Poisson.arrivalCount N A t ω} := by
      ext ω
      exact _root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA ht (hfin ω (t + 1))
    rw [hset]
    exact LevyStochCalc.Poisson.measurable_arrivalCount N A hℱ hA t measurableSet_Ici
end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end Finiteness

end LevyStochCalc.Poisson


