-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
-- name    : StochLean_Probability_Process_Path_RightLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:59.471009+00:00
-- url     : https://prove2.me/theorems/c31e6ba1-d96b-4886-a58e-0723693f44a9
-- title:
--   StochLean: Probability.Process.Path.RightLimit F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.Topology.Order.DenselyOrdered

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The right-limit process of a caglad input

Mathlib owns the strict-right-limit selector. Its limit and reconstruction identities
are proved on the caglad path domain. In general `H_(0+)` differs from `H_0`, so this
transformation is not a modification and does not normalize or overwrite the source initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def rightLimitProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Function.rightLim (fun s ↦ X s ω) t
end ProbabilityTheory


