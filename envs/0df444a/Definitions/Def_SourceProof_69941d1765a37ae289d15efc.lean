-- Prove2me | Definitions.Def_SourceProof_69941d1765a37ae289d15efc
-- name    : SourceProof_69941d1765a37ae289d15efc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:59.96392+00:00
-- url     : https://prove2.me/theorems/77052f41-90d8-4044-96b7-29507738ae84
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_Iic_zero

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

theorem _root_.Prove2MeSourceProof.h_69941d1765a37ae289d15efc : ν (Iic 0) = 0 := by
  have h := (Measure.le_iff'.mp hν) (Iic 0)
  simpa only [_root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5, sub_self, ENNReal.ofReal_zero,
    nonpos_iff_eq_zero] using h
end StochLean


