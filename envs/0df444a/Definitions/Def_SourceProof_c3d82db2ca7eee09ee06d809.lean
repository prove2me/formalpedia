-- Prove2me | Definitions.Def_SourceProof_c3d82db2ca7eee09ee06d809
-- name    : SourceProof_c3d82db2ca7eee09ee06d809
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:05.339273+00:00
-- url     : https://prove2.me/theorems/d06920fb-611a-5b94-a392-3fd2d5bd0c5a
-- title:
--   StochLean source theorem: StochLean.summable_stieltjes_jumps

import Definitions.Def_SourceProof_4e2804bfc01162ec6c386f31

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

theorem _root_.Prove2MeSourceProof.h_c3d82db2ca7eee09ee06d809 (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    Summable (fun s : Ioc 0 t ↦ f s - leftLim f s) := by
  have hsum : (∑' s : Ioc 0 t, ENNReal.ofReal (f s - leftLim f s)) ≠ ∞ := by
    rw [← _root_.Prove2MeSourceProof.h_4e2804bfc01162ec6c386f31]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.summable_toReal hsum
  simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono.leftLim_le le_rfl))] using h
end StochLean


