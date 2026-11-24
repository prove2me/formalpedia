-- Prove2me | Definitions.Def_StochLean_Probability_Process_StationaryIncrements_F000
-- name    : StochLean_Probability_Process_StationaryIncrements_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:49.723694+00:00
-- url     : https://prove2.me/theorems/73f95724-d1af-4518-bf61-9e4a39e34d72
-- title:
--   Stationary increments of a stochastic process
-- statement:
--   Each increment has the same distribution as the increment from time zero over the corresponding lag.

import Mathlib.Probability.IdentDistrib

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stationary increments
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [AddMonoid T] [MeasurableSpace E] [Sub E]

/-- A process has stationary increments when the law of an increment depends only on its lag.
The reference increment is `X t - X 0`; no assumption that `X 0 = 0` is built into the notion. -/
def HasStationaryIncrements (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ s t, IdentDistrib (fun ω ↦ X (s + t) ω - X s ω) (fun ω ↦ X t ω - X 0 ω) P P
namespace HasStationaryIncrements

variable {X : T → Ω → E} {P : Measure Ω}

end HasStationaryIncrements

end ProbabilityTheory


