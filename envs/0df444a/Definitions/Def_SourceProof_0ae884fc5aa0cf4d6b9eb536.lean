-- Prove2me | Definitions.Def_SourceProof_0ae884fc5aa0cf4d6b9eb536
-- name    : SourceProof_0ae884fc5aa0cf4d6b9eb536
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:02:36.259514+00:00
-- url     : https://prove2.me/theorems/c173a216-64bd-4494-8359-c82d8415e987
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.exitTime_le_iff
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]


theorem _root_.Prove2MeSourceProof.h_0ae884fc5aa0cf4d6b9eb536 {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by
  constructor
  · intro hle
    rw [LevyStochCalc.Probability.exitTime] at hle
    split_ifs at hle with h
    · have hmem := LevyStochCalc.Probability.csInf_exitSet_mem hX h
      have hst : sInf (LevyStochCalc.Probability.exitSet X k ω) ≤ t := by exact_mod_cast hle
      exact ⟨sInf (LevyStochCalc.Probability.exitSet X k ω), ⟨hmem.1, hst⟩, hmem.2⟩
    · exact absurd hle (by simp)
  · rintro ⟨s, ⟨hs0, hst⟩, hks⟩
    have hne : (LevyStochCalc.Probability.exitSet X k ω).Nonempty := ⟨s, hs0, hks⟩
    rw [LevyStochCalc.Probability.exitTime, if_pos hne]
    have hle : sInf (LevyStochCalc.Probability.exitSet X k ω) ≤ t :=
      le_trans (csInf_le (LevyStochCalc.Probability.bddBelow_exitSet X k ω) ⟨hs0, hks⟩) hst
    exact_mod_cast hle
end LevyStochCalc.Probability


