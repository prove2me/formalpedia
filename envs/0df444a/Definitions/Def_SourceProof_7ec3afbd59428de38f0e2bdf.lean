-- Prove2me | Definitions.Def_SourceProof_7ec3afbd59428de38f0e2bdf
-- name    : SourceProof_7ec3afbd59428de38f0e2bdf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:23.65425+00:00
-- url     : https://prove2.me/theorems/76d5da71-d707-4506-b802-e28f1325abf1
-- title:
--   StochLean source theorem: StochLean.measurable_kernel_singleton_of_finite_fibers

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002
import Definitions.Def_SourceProof_8541783849134de6ca757428
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable removal of the point atoms of a random finite measure

Joint singleton mass is the kernel integral of the measurable diagonal. The
zero-singleton-mass region is therefore jointly measurable, so its restriction
is again a measurable random measure. Only fiberwise finite mass is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
  (hκ : ∀ ω, IsFiniteMeasure (κ ω))

include hκ

theorem _root_.Prove2MeSourceProof.h_7ec3afbd59428de38f0e2bdf :
    Measurable fun p : Ω × ℝ≥0 ↦ κ p.1 {p.2} := by
  classical
  let η : Kernel (Ω × ℝ≥0) ℝ≥0 := ⟨fun p ↦ κ p.1, κ.measurable.comp measurable_fst⟩
  let f : (Ω × ℝ≥0) × ℝ≥0 → ℝ≥0∞ := fun p ↦ if p.1.2 = p.2 then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_eq_fun measurable_fst.snd measurable_snd) measurable_const measurable_const
  have h := _root_.Prove2MeSourceProof.h_8541783849134de6ca757428 (κ := η) (fun p ↦ hκ p.1) hf
  have heq (p : Ω × ℝ≥0) : (∫⁻ t, f (p, t) ∂η p) = κ p.1 {p.2} := by
    change (∫⁻ t, (if p.2 = t then (1 : ℝ≥0∞) else 0) ∂κ p.1) = _
    simpa only [Set.indicator, mem_singleton_iff, Pi.one_apply,
      eq_comm] using (lintegral_indicator_one (μ := κ p.1) (measurableSet_singleton p.2))
  simpa only [heq] using h
end StochLean


