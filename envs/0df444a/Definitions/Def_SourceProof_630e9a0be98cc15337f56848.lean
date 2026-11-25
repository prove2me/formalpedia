-- Prove2me | Definitions.Def_SourceProof_630e9a0be98cc15337f56848
-- name    : SourceProof_630e9a0be98cc15337f56848
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:26:01.656121+00:00
-- url     : https://prove2.me/theorems/b5495960-8529-4b16-80c7-725f51f2b76d
-- title:
--   StochLean source theorem: StochLean.rightContinuous_stieltjesSubmeasure_cumulative

import Definitions.Def_SourceProof_d9a8ee5c89d9353777a6b159
import Definitions.Def_SourceProof_df1932019c135a4024aed171

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

theorem _root_.Prove2MeSourceProof.h_630e9a0be98cc15337f56848 (s : ℝ≥0) :
    ContinuousWithinAt (fun t ↦ ν.real (Iic t)) (Ici s) s := by
  have hu : Tendsto (fun t ↦ ν.real (Iic s) + (f t - f s)) (𝓝[≥] s)
      (𝓝 (ν.real (Iic s))) := by
    simpa only [sub_self, add_zero] using
      tendsto_const_nhds.add ((f.right_continuous s).sub_const (f s))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact _root_.Prove2MeSourceProof.h_df1932019c135a4024aed171 f hν ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    linarith [_root_.Prove2MeSourceProof.h_d9a8ee5c89d9353777a6b159 f hν ht]
end StochLean


