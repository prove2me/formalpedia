-- Prove2me | Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf
-- name    : SourceProof_6fcc1c928f053fa880b8a3cf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:52.450812+00:00
-- url     : https://prove2.me/theorems/8ae8ed03-8965-481a-a6b4-9b38982462bb
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_Iic_lt_top

import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Mathlib.MeasureTheory.Measure.Real

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

theorem _root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf (t : ℝ≥0) : ν (Iic t) < ∞ := by
  apply lt_of_le_of_lt ((Measure.le_iff'.mp hν) _)
  rw [_root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]
  exact ENNReal.ofReal_lt_top
end StochLean


