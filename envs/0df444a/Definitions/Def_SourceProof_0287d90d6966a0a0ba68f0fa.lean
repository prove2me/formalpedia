-- Prove2me | Definitions.Def_SourceProof_0287d90d6966a0a0ba68f0fa
-- name    : SourceProof_0287d90d6966a0a0ba68f0fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:48.162002+00:00
-- url     : https://prove2.me/theorems/dc8c2e16-c2f4-46c9-b8bc-29f2208cf75a
-- title:
--   StochLean source theorem: StochLean.measurable_tprod_exponentialJumpFactor_Ioc_of_kernel_atoms

import Definitions.Def_SourceProof_911b993558830136570eb23c
import Definitions.Def_SourceProof_9dc5f658b159b2384b1b34af
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the actual jump product on random atom sets

The nonzero jump locations are supported by a measurable finite-fiber
kernel. Square summability supplies both the zero count and the complex
logarithm series. The guarded formula preserves zero and negative factors;
it proves measurability of the original product, not of a substitute.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_0287d90d6966a0a0ba68f0fa
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {u : Ω → ℝ≥0 → ℝ} (T : ℝ≥0)
    (hu : Measurable (uncurry u))
    (hs : ∀ ω, Summable (fun t : Set.Ioc 0 T ↦ u ω t ^ 2))
    (hzero : ∀ ω t, t ∈ Set.Ioc 0 T → κ ω {t} = 0 → u ω t = 0) :
    Measurable fun ω ↦ ∏' t : Set.Ioc 0 T, exponentialJumpFactor (u ω t) := by
  classical
  let v : Ω → ℝ≥0 → ℝ := fun ω ↦ (Set.Ioc 0 T).indicator (u ω)
  have hv : Measurable (uncurry v) :=
    Measurable.ite (measurable_snd measurableSet_Ioc) hu measurable_const
  have hvs (ω : Ω) : Summable (fun t ↦ v ω t ^ 2) := by
    have h := (summable_subtype_iff_indicator (f := fun t ↦ u ω t ^ 2)
      (s := Set.Ioc 0 T)).mp (hs ω)
    convert h using 1
    funext t
    by_cases ht : t ∈ Set.Ioc 0 T <;> simp [v, Set.indicator, ht]
  have hv0 (ω : Ω) (t : ℝ≥0) (ht : κ ω {t} = 0) : v ω t = 0 := by
    by_cases hm : t ∈ Set.Ioc 0 T
    · simp only [v, Set.indicator_of_mem hm, hzero ω t hm ht]
    · exact Set.indicator_of_notMem hm _
  have he (ω : Ω) : (∏' t, StochLean.exponentialJumpFactor (v ω t)) =
      ∏' t : Set.Ioc 0 T, StochLean.exponentialJumpFactor (u ω t) := by
    rw [tprod_subtype (Set.Ioc 0 T) (fun t ↦ StochLean.exponentialJumpFactor (u ω t))]
    apply tprod_congr
    intro t
    by_cases ht : t ∈ Set.Ioc 0 T <;>
      simp [v, Set.mulIndicator, ht, _root_.Prove2MeSourceProof.h_911b993558830136570eb23c]
  simpa only [he] using
    _root_.Prove2MeSourceProof.h_9dc5f658b159b2384b1b34af κ hκ hv hvs hv0
end StochLean


