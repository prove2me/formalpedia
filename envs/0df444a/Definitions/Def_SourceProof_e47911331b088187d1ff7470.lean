-- Prove2me | Definitions.Def_SourceProof_e47911331b088187d1ff7470
-- name    : SourceProof_e47911331b088187d1ff7470
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:24:58.528761+00:00
-- url     : https://prove2.me/theorems/5460c678-c208-4395-9532-ebdd51e54dc4
-- title:
--   LevyStochCalc source module: SourceProof_e47911331b088187d1ff7470
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exists_strictMono_enum_jumpTime` comes from the `LevyStochCalc.Poisson.JumpTimes` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002

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


theorem _root_.Prove2MeSourceProof.h_e47911331b088187d1ff7470 (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧
      Set.range e = {s : ℝ | ∃ i : ℕ, jumpTime N A i ω = (s : WithTop ℝ) ∧ s ≤ T} := by
  have himg : {s : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (s : WithTop ℝ) ∧ s ≤ T}
      = (fun i => sInf (LevyStochCalc.Poisson.jumpTimeSet N A i ω)) ''
          {i : ℕ | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (T : WithTop ℝ)} := by
    ext s
    constructor
    · rintro ⟨i, hi, hsT⟩
      refine ⟨i, ?_, ?_⟩
      · change LevyStochCalc.Poisson.jumpTime N A i ω ≤ (T : WithTop ℝ)
        rw [hi]
        exact_mod_cast hsT
      · rw [LevyStochCalc.Poisson.jumpTime] at hi
        split_ifs at hi with hne
        · exact_mod_cast hi
        · exact absurd hi (by simp)
    · rintro ⟨i, hi, rfl⟩
      have hi' : LevyStochCalc.Poisson.jumpTime N A i ω ≤ (T : WithTop ℝ) := hi
      have hne : (LevyStochCalc.Poisson.jumpTimeSet N A i ω).Nonempty := by
        by_contra hcon
        rw [LevyStochCalc.Poisson.jumpTime, if_neg hcon] at hi'
        exact absurd hi' (by simp)
      refine ⟨i, ?_, ?_⟩
      · rw [LevyStochCalc.Poisson.jumpTime, if_pos hne]
      · rw [LevyStochCalc.Poisson.jumpTime, if_pos hne] at hi'
        exact_mod_cast hi'
  rw [himg]
  obtain ⟨k, e, he, hrange⟩ := LevyStochCalc.Poisson.exists_strictMono_enum
    ((LevyStochCalc.Poisson.finite_setOf_jumpTime_le N A hA hT hfin).image
      fun i => sInf (LevyStochCalc.Poisson.jumpTimeSet N A i ω)).toFinset
  exact ⟨k, e, he, by rwa [Set.Finite.coe_toFinset] at hrange⟩
end Finiteness

end LevyStochCalc.Poisson


