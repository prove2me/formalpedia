-- Prove2me | Definitions.Def_SourceProof_264d677d5da3fcd447059c80
-- name    : SourceProof_264d677d5da3fcd447059c80
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:32.107512+00:00
-- url     : https://prove2.me/theorems/846630ff-759d-40fe-9881-8815cfc14644
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.jumpProcess

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source left limits and jumps

The Protter convention is `X_(0-) = 0`, not `X_0`. At positive times the
canonical Mathlib strict-left limit is reused; all mathematical limit identities
are proved on the cadlag domain. No limit property is asserted for an arbitrary
path on which a left limit does not exist.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Indistinguishable
theorem _root_.Prove2MeSourceProof.h_264d677d5da3fcd447059c80 {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) :
    Indistinguishable (jumpProcess X) (jumpProcess Y) P := by
  filter_upwards [h, (_root_.Prove2MeSourceProof.h_60e710b522febb5ad2df8d23 h)] with ω hω hl
  intro t
  change X t ω - ProbabilityTheory.leftLimitProcess X t ω =
    Y t ω - ProbabilityTheory.leftLimitProcess Y t ω
  rw [hω, hl]
end Indistinguishable

end ProbabilityTheory


