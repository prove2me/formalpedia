-- Prove2me | Definitions.Def_SourceProof_0a3c16aaf9407b6acdc7ca51
-- name    : SourceProof_0a3c16aaf9407b6acdc7ca51
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:03.701967+00:00
-- url     : https://prove2.me/theorems/752d1eb0-15e4-49b0-b002-b9021a510e67
-- title:
--   StochLean source theorem: StochLean.frechetSecondOrderRemainder_self

import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000

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

@[simp] theorem _root_.Prove2MeSourceProof.h_0a3c16aaf9407b6acdc7ca51 (f : E → ℝ) (a : E) :
    frechetSecondOrderRemainder f a a = 0 := by simp [StochLean.frechetSecondOrderRemainder]
end StochLean


