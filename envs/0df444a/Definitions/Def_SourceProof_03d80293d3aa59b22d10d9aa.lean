-- Prove2me | Definitions.Def_SourceProof_03d80293d3aa59b22d10d9aa
-- name    : SourceProof_03d80293d3aa59b22d10d9aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:00.123916+00:00
-- url     : https://prove2.me/theorems/546e3dfe-2230-4ad6-b727-0f307494477d
-- title:
--   StochLean source theorem: StochLean.continuous_quadraticTaylorSlope_of_contDiff

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
import Definitions.Def_SourceProof_9fbb5f16ba4c27a003e714f5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous quadratic Taylor quotient of a real C2 function

The diagonal is filled with one half of the second derivative, not the
totalized quotient's zero value. This is the coefficient of squared increments
in the exact finite-cell Taylor identity used for Ito's formula.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_03d80293d3aa59b22d10d9aa {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : ℝ × ℝ ↦ quadraticTaylorSlope f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact _root_.Prove2MeSourceProof.h_9fbb5f16ba4c27a003e714f5 hf
    continuous_fst.continuousAt continuous_snd.continuousAt
end StochLean


