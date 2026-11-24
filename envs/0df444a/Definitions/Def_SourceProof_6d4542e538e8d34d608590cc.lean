-- Prove2me | Definitions.Def_SourceProof_6d4542e538e8d34d608590cc
-- name    : SourceProof_6d4542e538e8d34d608590cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:32.188248+00:00
-- url     : https://prove2.me/theorems/d11cc80f-0da5-4123-8f73-eac3ef551ad5
-- title:
--   StochLean source theorem: StochLean.exponentialJumpFactor_neg_one

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

@[simp] theorem _root_.Prove2MeSourceProof.h_6d4542e538e8d34d608590cc : exponentialJumpFactor (-1) = 0 := by
  simp [StochLean.exponentialJumpFactor]
end StochLean


