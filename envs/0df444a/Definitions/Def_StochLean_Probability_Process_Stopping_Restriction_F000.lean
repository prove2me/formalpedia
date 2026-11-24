-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000
-- name    : StochLean_Probability_Process_Stopping_Restriction_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:10.285318+00:00
-- url     : https://prove2.me/theorems/338df4fb-6887-4c55-a93c-4332a0c54586
-- title:
--   StochLean: Probability.Process.Stopping.Restriction F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Graph_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting a stopping time to an event

Protter III.2's `T_A` is `T` on `A` and infinity off `A`. Stopping requires
`A ∈ F_T`, not initial measurability. The graph restriction is an exact
finite-time identity, including the zero-time section.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

noncomputable def restrictedStoppingTime (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    Ω → WithTop ℝ≥0 := by
  classical
  exact fun ω ↦ if ω ∈ A then τ ω else ⊤
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


