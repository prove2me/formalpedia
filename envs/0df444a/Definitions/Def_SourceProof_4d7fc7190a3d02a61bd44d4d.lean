-- Prove2me | Definitions.Def_SourceProof_4d7fc7190a3d02a61bd44d4d
-- name    : SourceProof_4d7fc7190a3d02a61bd44d4d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:05:31.894931+00:00
-- url     : https://prove2.me/theorems/08ac7250-297a-593b-b0b4-057f561c8f18
-- title:
--   StochLean source theorem: StochLean.summable_abs_frechet_second_order_jump_remainders

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_0a4c4ca9908aae52a5fd404b
import Definitions.Def_SourceProof_deb465799a9f476945dd8c4f
import Definitions.Def_SourceProof_f43dd7a81208ca8c2cdabd61
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute vector Taylor jump series from square-summable jump norms

Local compact bounds control the actual first- and second-order corrections.
The original path is not assumed to have finite variation.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {x : ℝ≥0 → E} {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_4d7fc7190a3d02a61bd44d4d [NormedSpace ℝ E]
    (hx : IsCadlagPath x) (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦ |frechetSecondOrderRemainder f (leftLim x s) (x s)|) := by
  simpa only [_root_.Prove2MeSourceProof.h_deb465799a9f476945dd8c4f] using
    _root_.Prove2MeSourceProof.h_f43dd7a81208ca8c2cdabd61 hx hs
      (_root_.Prove2MeSourceProof.h_0a4c4ca9908aae52a5fd404b hf)
end StochLean


