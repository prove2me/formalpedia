-- Prove2me | Definitions.Def_SourceProof_d4a99c0e323c66ca321b35d5
-- name    : SourceProof_d4a99c0e323c66ca321b35d5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:00.57486+00:00
-- url     : https://prove2.me/theorems/f83f02df-b21e-511a-9bc0-d7a9dbfab19f
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_real_increment

import Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf

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

theorem _root_.Prove2MeSourceProof.h_d4a99c0e323c66ca321b35d5 {s t : ℝ≥0} (hst : s ≤ t) :
    ν.real (Iic t) - ν.real (Iic s) = ν.real (Ioc s t) := by
  rw [← Iic_sdiff_Iic]
  exact (measureReal_sdiff (Iic_subset_Iic.mpr hst) measurableSet_Iic
    (_root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f hν t).ne).symm
end StochLean


