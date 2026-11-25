-- Prove2me | Definitions.Def_SourceProof_e53a0a54f0755719030aa5d3
-- name    : SourceProof_e53a0a54f0755719030aa5d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:40.190985+00:00
-- url     : https://prove2.me/theorems/cdeb6bd2-3a3b-50fc-a529-ecce61c2605e
-- title:
--   StochLean source theorem: StochLean.multipliable_exponentialJumpFactor

import Definitions.Def_StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000
import Definitions.Def_SourceProof_c00d36002cf69560fd2a8d00

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

theorem _root_.Prove2MeSourceProof.h_e53a0a54f0755719030aa5d3 {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) : Multipliable (fun i ↦ exponentialJumpFactor (u i)) := by
  have h := Real.multipliable_one_add_of_summable
    (_root_.Prove2MeSourceProof.h_c00d36002cf69560fd2a8d00 hu).of_abs
  exact h.congr (fun _ ↦ by ring)
end StochLean


