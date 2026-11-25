-- Prove2me | Definitions.Def_SourceProof_97ac1be72f56ff014f1c8e3a
-- name    : SourceProof_97ac1be72f56ff014f1c8e3a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:34.67842+00:00
-- url     : https://prove2.me/theorems/2b4e4cdf-0c20-493e-98ab-dca445d4f5fd
-- title:
--   StochLean source theorem: StochLean.stieltjes_continuous_jump_decomposition

import Definitions.Def_SourceProof_0339642eaaa29ff45e7162b6
import Definitions.Def_SourceProof_4e8110606e54c4a30322b7f7

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The jump part is the actual sum of positive-time jumps

The sum is indexed by every time in `(0,t]`, not an assumed enumeration of
jumps. Countable support and finite mass on compact intervals give summability.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_97ac1be72f56ff014f1c8e3a (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f t = f 0 + stieltjesContinuousPart f t + ∑' s : Ioc 0 t, (f s - leftLim f s) := by
  rw [← _root_.Prove2MeSourceProof.h_4e8110606e54c4a30322b7f7]
  linarith [_root_.Prove2MeSourceProof.h_0339642eaaa29ff45e7162b6 f t]
end StochLean


