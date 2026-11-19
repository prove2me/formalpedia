-- Prove2me | Definitions.Def_SourceProof_ae47f47307f762c81c3ce31c
-- name    : SourceProof_ae47f47307f762c81c3ce31c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:03:19.290204+00:00
-- url     : https://prove2.me/theorems/a921b382-6d71-4a83-b5d1-5e6ca15a422e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.exists_lt_exitTime
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000
import Definitions.Def_SourceProof_0ae884fc5aa0cf4d6b9eb536

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


theorem _root_.Prove2MeSourceProof.h_ae47f47307f762c81c3ce31c {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω := by
  obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
    (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
  obtain ⟨K, hK⟩ := exists_nat_gt ‖X ω s₀‖
  refine ⟨K, fun k hk => ?_⟩
  rcases lt_or_ge (t : WithTop ℝ) (LevyStochCalc.Probability.exitTime X (k : ℝ) ω) with hlt | hle
  · exact hlt
  · exfalso
    obtain ⟨s, hs, hks⟩ := (_root_.Prove2MeSourceProof.h_0ae884fc5aa0cf4d6b9eb536 hX (k : ℝ) t).1 hle
    have h1 : ‖X ω s‖ ≤ ‖X ω s₀‖ := hmax hs
    have h2 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
end LevyStochCalc.Probability


