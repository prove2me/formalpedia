-- Prove2me | Definitions.Def_SourceProof_deb465799a9f476945dd8c4f
-- name    : SourceProof_deb465799a9f476945dd8c4f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:24.117801+00:00
-- url     : https://prove2.me/theorems/4ef413f1-0c04-485e-a210-7a5ff7edf442
-- title:
--   StochLean source theorem: StochLean.frechetTaylorErrorCoefficient_mul_norm_sq

import Definitions.Def_SourceProof_0a3c16aaf9407b6acdc7ca51
import Definitions.Def_SourceProof_6c8628105866f38712113f22

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

theorem _root_.Prove2MeSourceProof.h_deb465799a9f476945dd8c4f (f : E → ℝ) (a b : E) :
    frechetTaylorErrorCoefficient f a b * ‖b - a‖ ^ 2 = frechetSecondOrderRemainder f a b := by
  by_cases h : b = a
  · subst b
    simp
  · exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))
end StochLean


