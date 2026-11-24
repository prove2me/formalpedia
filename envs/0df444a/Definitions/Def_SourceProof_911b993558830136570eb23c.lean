-- Prove2me | Definitions.Def_SourceProof_911b993558830136570eb23c
-- name    : SourceProof_911b993558830136570eb23c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:28.807008+00:00
-- url     : https://prove2.me/theorems/78ffa062-34bc-418d-8c15-5612114c3de3
-- title:
--   StochLean source theorem: StochLean.exponentialJumpFactor_zero

import Definitions.Def_StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The jump factor of the Doleans--Dade exponential

Square summability implies absolute summability of the deviations from one.
This proves convergence of the actual product, including zero and negative
factors; logarithms are not taken across those exceptional factors.
-/

@[expose] public section

namespace StochLean

@[simp] theorem _root_.Prove2MeSourceProof.h_911b993558830136570eb23c : exponentialJumpFactor 0 = 1 := by
  simp [StochLean.exponentialJumpFactor]
end StochLean


