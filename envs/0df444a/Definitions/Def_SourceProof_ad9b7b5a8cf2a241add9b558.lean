-- Prove2me | Definitions.Def_SourceProof_ad9b7b5a8cf2a241add9b558
-- name    : SourceProof_ad9b7b5a8cf2a241add9b558
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:59.559907+00:00
-- url     : https://prove2.me/theorems/87a114c2-13fc-480e-8367-c0c169de8916
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_zero

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
import Definitions.Def_SourceProof_69941d1765a37ae289d15efc

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

@[simp] theorem _root_.Prove2MeSourceProof.h_ad9b7b5a8cf2a241add9b558 : stieltjesSubmeasure f hν 0 = 0 := by
  change (ν (Iic 0)).toReal = 0
  rw [_root_.Prove2MeSourceProof.h_69941d1765a37ae289d15efc f hν, ENNReal.toReal_zero]
end StochLean


