-- Prove2me | Definitions.Def_SourceProof_0c7e85b4037c170c4bb0381a
-- name    : SourceProof_0c7e85b4037c170c4bb0381a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:58:37.190467+00:00
-- url     : https://prove2.me/theorems/c11ccefa-eaf3-4b23-bb9e-b0bbf5ed1140
-- title:
--   LevyStochCalc source proof: LevyStochCalc.abs_setIntegral_Ioc_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments of the integral of a bounded function

The drift part of an Itô process is `t ↦ ∫_0^t b_s ds`. Its increment across a cell is the
integral over that cell, and is bounded by the bound on `b` times the cell length.

## Main statements

* `LevyStochCalc.integrableOn_of_bounded_of_measurable` — a bounded measurable function is
  integrable on any set of finite measure.
* `LevyStochCalc.setIntegral_Icc_sub_Icc` — `∫_{[0,b]} − ∫_{[0,a]} = ∫_{(a,b]}`.
* `LevyStochCalc.abs_setIntegral_Ioc_le` — `|∫_{(a,b]} f| ≤ B·(b − a)`.
* `LevyStochCalc.abs_setIntegral_Icc_sub_le` — `t ↦ ∫_{[0,t]} f` is `B`-Lipschitz.
* `LevyStochCalc.continuous_setIntegral_Icc` — hence continuous.
* `LevyStochCalc.measurable_setIntegral` — the integral over a fixed set is measurable in
  the parameter.
* `LevyStochCalc.measurable_setIntegral_Ioc` — the window integral is measurable in the
  parameter.
-/

namespace LevyStochCalc

open MeasureTheory


theorem _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by
  have hB0 : (0 : ℝ) ≤ B := (abs_nonneg (f a)).trans (hB a)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    LevyStochCalc.integrableOn_of_bounded_of_measurable hf hB (by simp)
  have habs : |∫ s in Set.Ioc a b, f s ∂volume| ≤ ∫ s in Set.Ioc a b, |f s| ∂volume := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a b)) f
  refine habs.trans ?_
  have hle : ∫ s in Set.Ioc a b, |f s| ∂volume ≤ ∫ _s in Set.Ioc a b, B ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint.abs
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => hB u
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)
end LevyStochCalc


