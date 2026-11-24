-- Prove2me | Definitions.Def_SourceProof_6a699b84e118f7439b9a72bc
-- name    : SourceProof_6a699b84e118f7439b9a72bc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:24.658029+00:00
-- url     : https://prove2.me/theorems/6e4e6c48-f211-45c4-89fd-a5e6b5611673
-- title:
--   StochLean source theorem: StochLean.contDiff_exponentialJumpFactor

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

theorem _root_.Prove2MeSourceProof.h_6a699b84e118f7439b9a72bc {n : WithTop ℕ∞} :
    ContDiff ℝ n exponentialJumpFactor := by
  unfold StochLean.exponentialJumpFactor
  fun_prop
end StochLean


