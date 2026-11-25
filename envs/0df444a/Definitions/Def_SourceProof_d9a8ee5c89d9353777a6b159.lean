-- Prove2me | Definitions.Def_SourceProof_d9a8ee5c89d9353777a6b159
-- name    : SourceProof_d9a8ee5c89d9353777a6b159
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:25.832078+00:00
-- url     : https://prove2.me/theorems/42ff746c-29e6-41a8-b9d7-9312d5e00a42
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_real_increment_le

import Definitions.Def_SourceProof_d4a99c0e323c66ca321b35d5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A genuine Stieltjes realization of a submeasure

A measure dominated by a half-line Stieltjes measure is finite on every initial
interval and has no mass at zero. Its cumulative mass is right-continuous by
the original path's right continuity and the domination of interval increments.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StochLean

variable (f : StieltjesFunction ℝ≥0) {ν : Measure ℝ≥0} (hν : ν ≤ f.measure)

include hν

theorem _root_.Prove2MeSourceProof.h_d9a8ee5c89d9353777a6b159 {s t : ℝ≥0} (hst : s ≤ t) :
    ν.real (Iic t) - ν.real (Iic s) ≤ f t - f s := by
  rw [_root_.Prove2MeSourceProof.h_d4a99c0e323c66ca321b35d5 f hν hst]
  have h := ENNReal.toReal_mono
    (show f.measure (Ioc s t) ≠ ∞ from measure_Ioc_lt_top.ne)
    ((Measure.le_iff'.mp hν) (Ioc s t))
  simpa only [measureReal_def, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hst))] using h
end StochLean


