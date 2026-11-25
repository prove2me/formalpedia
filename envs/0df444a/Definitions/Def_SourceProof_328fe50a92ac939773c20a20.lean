-- Prove2me | Definitions.Def_SourceProof_328fe50a92ac939773c20a20
-- name    : SourceProof_328fe50a92ac939773c20a20
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:51.461498+00:00
-- url     : https://prove2.me/theorems/53741246-0950-4686-b948-7836e712e3d4
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.leftLimitProcess_mul

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_b1bc6055f79188919ce22dd1
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Multiplication of source left limits

Both source left limits vanish at zero, so multiplication commutes with the
left-limit operation at every time, not only at positive times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_328fe50a92ac939773c20a20 {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) :
    Indistinguishable (leftLimitProcess (X * Y))
      (leftLimitProcess X * leftLimitProcess Y) P := by
  filter_upwards [hX, hY] with ω hx hy t
  exact (_root_.Prove2MeSourceProof.h_b1bc6055f79188919ce22dd1 hx) hy t
end HasCadlagPaths

end ProbabilityTheory


