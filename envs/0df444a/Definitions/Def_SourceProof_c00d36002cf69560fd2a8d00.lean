-- Prove2me | Definitions.Def_SourceProof_c00d36002cf69560fd2a8d00
-- name    : SourceProof_c00d36002cf69560fd2a8d00
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:55:08.589236+00:00
-- url     : https://prove2.me/theorems/2847f5a8-dfae-4300-b321-a82498014e62
-- title:
--   StochLean source theorem: StochLean.summable_abs_exponentialJumpFactor_sub_one

import Definitions.Def_SourceProof_6a699b84e118f7439b9a72bc
import Definitions.Def_SourceProof_84381ae97d0c3f859915503a
import Definitions.Def_SourceProof_911b993558830136570eb23c
import Definitions.Def_SourceProof_c91e390c2a73a5dcb2127821

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

theorem _root_.Prove2MeSourceProof.h_c00d36002cf69560fd2a8d00 {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ |exponentialJumpFactor (u i) - 1|) := by
  have hd : deriv StochLean.exponentialJumpFactor 0 = 0 := by
    simpa using (_root_.Prove2MeSourceProof.h_c91e390c2a73a5dcb2127821 0).deriv
  simpa only [_root_.Prove2MeSourceProof.h_911b993558830136570eb23c, hd, zero_mul, sub_zero] using
    _root_.Prove2MeSourceProof.h_84381ae97d0c3f859915503a hu _root_.Prove2MeSourceProof.h_6a699b84e118f7439b9a72bc
end StochLean


