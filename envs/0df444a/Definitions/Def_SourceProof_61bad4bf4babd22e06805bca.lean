-- Prove2me | Definitions.Def_SourceProof_61bad4bf4babd22e06805bca
-- name    : SourceProof_61bad4bf4babd22e06805bca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:26:02.784988+00:00
-- url     : https://prove2.me/theorems/90e756b1-53e6-40e0-bffe-cf5abaa4499c
-- title:
--   StochLean source theorem: StochLean.summable_complex_log_exponentialJumpFactor

import Definitions.Def_SourceProof_c00d36002cf69560fd2a8d00

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A zero-guarded complex-log representation of the real jump product

The principal complex logarithm retains the sign of negative factors.
Its convergent exponential represents the real product only when every
factor is nonzero. A separately summable count of jumps of size -1 supplies
the zero guard. This representation is intended for measurability proofs,
not as a replacement for the canonical real product definition.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_61bad4bf4babd22e06805bca {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ Complex.log (exponentialJumpFactor (u i) : ℂ)) := by
  have h := Complex.summable_log_one_add_of_summable
    (Complex.summable_ofReal.mpr (_root_.Prove2MeSourceProof.h_c00d36002cf69560fd2a8d00 hu).of_abs)
  apply h.congr
  intro i
  congr 1
  push_cast
  ring
end StochLean


