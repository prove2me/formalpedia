-- Prove2me | Definitions.Def_SourceProof_c91e390c2a73a5dcb2127821
-- name    : SourceProof_c91e390c2a73a5dcb2127821
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:42.869801+00:00
-- url     : https://prove2.me/theorems/b22e0462-4215-4a7a-bc3b-71af219a621a
-- title:
--   StochLean source theorem: StochLean.hasDerivAt_exponentialJumpFactor

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

theorem _root_.Prove2MeSourceProof.h_c91e390c2a73a5dcb2127821 (u : ℝ) :
    HasDerivAt exponentialJumpFactor (-u * Real.exp (-u)) u := by
  have h : HasDerivAt (fun x : ℝ ↦ (1 + x) * Real.exp (-x))
      (1 * Real.exp (-u) + (1 + u) * (Real.exp (-u) * (-1))) u :=
    ((hasDerivAt_id u).const_add 1).mul ((hasDerivAt_id u).neg.exp)
  unfold StochLean.exponentialJumpFactor
  convert h using 1
  ring
end StochLean


