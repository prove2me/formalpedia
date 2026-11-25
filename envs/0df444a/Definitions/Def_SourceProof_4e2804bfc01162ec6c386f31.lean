-- Prove2me | Definitions.Def_SourceProof_4e2804bfc01162ec6c386f31
-- name    : SourceProof_4e2804bfc01162ec6c386f31
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:25.534706+00:00
-- url     : https://prove2.me/theorems/b3c4dfbd-536c-457e-ba0e-da8d3d362e77
-- title:
--   StochLean source theorem: StochLean.stieltjesJumpPart_ofReal_eq_tsum

import Definitions.Def_SourceProof_b62997f1362a9ceb2e5846fe
import Definitions.Def_SourceProof_d525a237722b981ed0b6d6ee
import Definitions.Def_SourceProof_ef871b7f247732b34ba06d39

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

theorem _root_.Prove2MeSourceProof.h_4e2804bfc01162ec6c386f31 (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    ENNReal.ofReal (stieltjesJumpPart f t) =
      ∑' s : Ioc 0 t, ENNReal.ofReal (f s - leftLim f s) := by
  calc
    _ = (StochLean.stieltjesJumpPart f).measure (Ioc 0 t) := by
      rw [StieltjesFunction.measure_Ioc, _root_.Prove2MeSourceProof.h_d525a237722b981ed0b6d6ee, sub_zero]
    _ = StochLean.pointAtomicPart f.measure (Ioc 0 t) := by rw [_root_.Prove2MeSourceProof.h_ef871b7f247732b34ba06d39]
    _ = ∑' s : Ioc 0 t, f.measure {(s : ℝ≥0)} :=
      _root_.Prove2MeSourceProof.h_b62997f1362a9ceb2e5846fe _ measurableSet_Ioc
    _ = _ := by simp_rw [StieltjesFunction.measure_singleton]
end StochLean


