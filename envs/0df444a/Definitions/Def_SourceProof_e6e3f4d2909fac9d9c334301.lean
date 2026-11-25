-- Prove2me | Definitions.Def_SourceProof_e6e3f4d2909fac9d9c334301
-- name    : SourceProof_e6e3f4d2909fac9d9c334301
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:15.528809+00:00
-- url     : https://prove2.me/theorems/774ad68a-ac9d-41a4-a921-cb464e1d1ef3
-- title:
--   StochLean source theorem: StochLean.stieltjesSubmeasure_measure

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
import Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf
import Definitions.Def_SourceProof_ce8d23ea9acd431df11cba69

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

theorem _root_.Prove2MeSourceProof.h_e6e3f4d2909fac9d9c334301 : (stieltjesSubmeasure f hν).measure = ν := by
  have hu : (⋃ n : ℕ, Iic (n : ℝ≥0)) = univ := by
    ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil t, Nat.le_ceil t⟩
  apply Measure.ext_of_iUnion_eq_univ hu
  intro n
  let μ := (StochLean.stieltjesSubmeasure f hν).measure
  have : IsFiniteMeasure (μ.restrict (Iic (n : ℝ≥0))) :=
    ⟨by rw [Measure.restrict_apply_univ, _root_.Prove2MeSourceProof.h_ce8d23ea9acd431df11cba69]
        exact _root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f hν n⟩
  apply Measure.ext_of_Iic
  intro t
  simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
    _root_.Prove2MeSourceProof.h_ce8d23ea9acd431df11cba69]
end StochLean


