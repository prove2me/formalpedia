-- Prove2me | Definitions.Def_SourceProof_23352e256ccbe406f366e43d
-- name    : SourceProof_23352e256ccbe406f366e43d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:56.189152+00:00
-- url     : https://prove2.me/theorems/cd895b4f-d8f5-443d-89fa-45c04683323e
-- title:
--   StochLean source theorem: StochLean.measurable_pointAtomicPart_of_finite_fibers

import Definitions.Def_SourceProof_7ec3afbd59428de38f0e2bdf
import Definitions.Def_SourceProof_8541783849134de6ca757428
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable point-atomic parts and their actual integral series

The atom locations may vary with the sample. Joint singleton mass gives
a measurable restriction without choosing an enumeration. Fiberwise
finite mass is sufficient; no deterministic bound on total mass is imposed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
  (hκ : ∀ ω, IsFiniteMeasure (κ ω))

include hκ

theorem _root_.Prove2MeSourceProof.h_23352e256ccbe406f366e43d :
    Measurable fun ω ↦ pointAtomicPart (κ ω) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let S : Set (Ω × ℝ≥0) := {p | p.2 ∈ s ∧ κ p.1 {p.2} ≠ 0}
  have hS : MeasurableSet S :=
    (measurable_snd hs).inter
      (measurableSet_eq_fun (_root_.Prove2MeSourceProof.h_7ec3afbd59428de38f0e2bdf κ hκ)
        measurable_const).compl
  have h := _root_.Prove2MeSourceProof.h_8541783849134de6ca757428 hκ
    (show Measurable (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) from measurable_const.indicator hS)
  have he (ω : Ω) : (∫⁻ t, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ω, t) ∂κ ω) =
      StochLean.pointAtomicPart (κ ω) s := by
    rw [lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hS 1,
      one_mul, StochLean.pointAtomicPart, Measure.restrict_apply hs]
    rfl
  simpa only [he] using h
end StochLean


