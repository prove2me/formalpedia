-- Prove2me | Definitions.Def_SourceProof_df1932019c135a4024aed171
-- name    : SourceProof_df1932019c135a4024aed171
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:32.394144+00:00
-- url     : https://prove2.me/theorems/f9edcbed-c856-431f-906f-1fad517762b1
-- title:
--   StochLean source theorem: StochLean.monotone_stieltjesSubmeasure_cumulative

import Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.LeftRight

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

theorem _root_.Prove2MeSourceProof.h_df1932019c135a4024aed171 : Monotone (fun t ↦ ν.real (Iic t)) := by
  intro s t hst
  exact measureReal_mono (Iic_subset_Iic.mpr hst) (_root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f hν t).ne
end StochLean


