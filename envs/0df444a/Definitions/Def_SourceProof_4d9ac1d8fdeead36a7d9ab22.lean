-- Prove2me | Definitions.Def_SourceProof_4d9ac1d8fdeead36a7d9ab22
-- name    : SourceProof_4d9ac1d8fdeead36a7d9ab22
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:40.651838+00:00
-- url     : https://prove2.me/theorems/07ce21f0-435d-4c3e-a631-3a160225450c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_const_mul

import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_555fdf58cf2acc34e4941dfb
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of source left limits and jumps

Continuous scalar transformations must preserve zero to commute with the
source left limit at every time, including the special time-zero value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_4d9ac1d8fdeead36a7d9ab22 (hX : IsCadlagPath (X · ω))
    (c : ℝ) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ c * X s v) t ω = c * jumpProcess X t ω := by
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply,
    (_root_.Prove2MeSourceProof.h_555fdf58cf2acc34e4941dfb (f := fun x ↦ c * x) hX)
      (continuous_const.mul continuous_id) (mul_zero c) t]
  ring
end IsCadlagPath

end ProbabilityTheory


