-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
-- name    : StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:35:38.882118+00:00
-- url     : https://prove2.me/theorems/24803e70-e0fb-44c4-b5e5-a8f1097b6b59
-- title:
--   StochLean: Analysis.PathVariation.StieltjesSubmeasure F000

import Definitions.Def_SourceProof_630e9a0be98cc15337f56848
import Definitions.Def_SourceProof_df1932019c135a4024aed171
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

noncomputable def stieltjesSubmeasure : StieltjesFunction ℝ≥0 where
  toFun t := ν.real (Iic t)
  mono' := _root_.Prove2MeSourceProof.h_df1932019c135a4024aed171 f hν
  right_continuous' := _root_.Prove2MeSourceProof.h_630e9a0be98cc15337f56848 f hν
end StochLean


