-- Prove2me | Definitions.Def_SourceProof_ce8d23ea9acd431df11cba69
-- name    : SourceProof_ce8d23ea9acd431df11cba69
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:48.090815+00:00
-- url     : https://prove2.me/theorems/d46ed3f5-2f79-402a-9856-75c8e994eaae
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_measure_Iic

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf
import Definitions.Def_SourceProof_ad9b7b5a8cf2a241add9b558

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

theorem _root_.Prove2MeSourceProof.h_ce8d23ea9acd431df11cba69 (t : ℝ≥0) :
    (stieltjesSubmeasure f hν).measure (Iic t) = ν (Iic t) := by
  rw [_root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5, _root_.Prove2MeSourceProof.h_ad9b7b5a8cf2a241add9b558, sub_zero]
  exact ofReal_measureReal (_root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f hν t).ne
end StochLean


