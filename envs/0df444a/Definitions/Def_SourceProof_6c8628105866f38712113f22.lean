-- Prove2me | Definitions.Def_SourceProof_6c8628105866f38712113f22
-- name    : SourceProof_6c8628105866f38712113f22
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:22.197581+00:00
-- url     : https://prove2.me/theorems/b1d86721-8d61-4b29-8e38-08674fe5083d
-- title:
--   StochLean source theorem: StochLean.frechetTaylorErrorCoefficient_self

import Definitions.Def_SourceProof_0a3c16aaf9407b6acdc7ca51

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

@[simp] theorem _root_.Prove2MeSourceProof.h_6c8628105866f38712113f22 (f : E → ℝ) (a : E) :
    frechetTaylorErrorCoefficient f a a = 0 := by simp [StochLean.frechetTaylorErrorCoefficient]
end StochLean


