-- Prove2me | Definitions.Def_SourceProof_1849eb0e6619cf2c91089130
-- name    : SourceProof_1849eb0e6619cf2c91089130
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:28:11.806181+00:00
-- url     : https://prove2.me/theorems/380ab75f-a1ae-4319-938f-cd5fea3cbe92
-- title:
--   LevyStochCalc source module: SourceProof_1849eb0e6619cf2c91089130
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.jumpTime_lt_iff` comes from the `LevyStochCalc.Poisson.JumpTimes` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_1849eb0e6619cf2c91089130 (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω < (t : WithTop ℝ)
      ↔ ∃ s : ℝ, 0 ≤ s ∧ s < t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A s ω := by
  rw [LevyStochCalc.Poisson.jumpTime]
  split_ifs with hne
  · constructor
    · intro hlt
      have hst : sInf (LevyStochCalc.Poisson.jumpTimeSet N A i ω) < t := by exact_mod_cast hlt
      obtain ⟨s, hs, hst'⟩ := exists_lt_of_csInf_lt hne hst
      exact ⟨s, hs.1, hst', hs.2⟩
    · rintro ⟨s, hs0, hst, hcount⟩
      have hle : sInf (LevyStochCalc.Poisson.jumpTimeSet N A i ω) ≤ s :=
        csInf_le (LevyStochCalc.Poisson.bddBelow_jumpTimeSet N A i ω) ⟨hs0, hcount⟩
      exact_mod_cast lt_of_le_of_lt hle hst
  · constructor
    · intro hlt
      exact absurd hlt (by simp)
    · rintro ⟨s, hs0, _, hcount⟩
      exact absurd ⟨s, hs0, hcount⟩ hne
end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end Finiteness

end LevyStochCalc.Poisson


