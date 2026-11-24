-- Prove2me | Definitions.Def_SourceProof_557830813c6833ac5ce8fc92
-- name    : SourceProof_557830813c6833ac5ce8fc92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:36.17284+00:00
-- url     : https://prove2.me/theorems/299f728a-15d2-48b9-8a10-845efd65aa83
-- title:
--   StochLean source theorem: StochLean.measurable_pointAtomicIntegral_of_finite_fibers

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
import Definitions.Def_SourceProof_23352e256ccbe406f366e43d
import Definitions.Def_SourceProof_2f4a84a27df946e0a2e71707
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral

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

theorem _root_.Prove2MeSourceProof.h_557830813c6833ac5ce8fc92
    {f : Ω → ℝ≥0 → ℝ} (hf : Measurable (uncurry f)) :
    Measurable fun ω ↦ ∫ t, f ω t ∂pointAtomicPart (κ ω) := by
  let η : Kernel Ω ℝ≥0 := ⟨fun ω ↦ StochLean.pointAtomicPart (κ ω),
    _root_.Prove2MeSourceProof.h_23352e256ccbe406f366e43d κ hκ⟩
  have hη (ω : Ω) : IsFiniteMeasure (η ω) := by
    let : IsFiniteMeasure (κ ω) := hκ ω
    change IsFiniteMeasure ((κ ω).restrict (StochLean.pointAtomSet (κ ω)))
    infer_instance
  exact (_root_.Prove2MeSourceProof.h_2f4a84a27df946e0a2e71707 η hη
    hf.stronglyMeasurable).measurable
end StochLean


