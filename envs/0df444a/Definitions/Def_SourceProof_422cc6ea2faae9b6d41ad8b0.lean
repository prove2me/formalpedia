-- Prove2me | Definitions.Def_SourceProof_422cc6ea2faae9b6d41ad8b0
-- name    : SourceProof_422cc6ea2faae9b6d41ad8b0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:25.751134+00:00
-- url     : https://prove2.me/theorems/16158caa-0884-4a27-b134-0cf82c5d1d0c
-- title:
--   StochLean source theorem: StochLean.measurable_jump_of_locallyBoundedVariation

import Definitions.Def_SourceProof_82c6d1dbda060237d4fd2c23

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable support and absolute summability of FV jumps

The actual positive and negative Stieltjes measures control the jumps. No
enumeration of jumps or summability assumption is supplied by the caller.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

variable {x : ℝ≥0 → ℝ} (hv : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

include hv hr

theorem _root_.Prove2MeSourceProof.h_422cc6ea2faae9b6d41ad8b0 :
    Measurable (fun t ↦ x t - leftLim x t) := by
  apply measurable_const.measurable_of_countable_ne (f := fun _ : ℝ≥0 ↦ (0 : ℝ))
  simpa only [ne_comm, support, mem_ofPred_eq] using
    _root_.Prove2MeSourceProof.h_82c6d1dbda060237d4fd2c23 hv hr
end StochLean


