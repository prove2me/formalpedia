-- Prove2me | Definitions.Def_SourceProof_d853fc6b74b1edd2bebb09da
-- name    : SourceProof_d853fc6b74b1edd2bebb09da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:45.035586+00:00
-- url     : https://prove2.me/theorems/e69fc002-4f27-4f3f-9cea-7ea51abec7cc
-- title:
--   StochLean source theorem: StochLean.summable_stieltjes_atom_mul_of_bounded

import Definitions.Def_SourceProof_c3d82db2ca7eee09ee06d809
import Definitions.Def_SourceProof_cdf76879721d1dc6620e7985
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The Stieltjes integral of FV jumps is their squared-jump series

Both Jordan component integrals and both series are genuinely integrable and
summable. The real-valued `tsum` is not used to conceal a divergent series.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_d853fc6b74b1edd2bebb09da (A : StieltjesFunction ℝ≥0)
    (T : ℝ≥0) {f : ℝ≥0 → ℝ} {C : ℝ} (hC : ∀ t ∈ Ioc 0 T, |f t| ≤ C) :
    Summable (fun t : Ioc 0 T ↦ A.measure.real {(t : ℝ≥0)} * f t) := by
  apply ((_root_.Prove2MeSourceProof.h_c3d82db2ca7eee09ee06d809 A T).mul_right C).of_norm_bounded
  intro t
  simp only [norm_mul, Real.norm_eq_abs, measureReal_def, _root_.Prove2MeSourceProof.h_cdf76879721d1dc6620e7985,
    abs_of_nonneg (sub_nonneg.mpr (A.mono.leftLim_le (x := (t : ℝ≥0)) le_rfl))]
  exact mul_le_mul_of_nonneg_left (hC t t.2) (sub_nonneg.mpr (A.mono.leftLim_le le_rfl))
end StochLean


