-- Prove2me | Definitions.Def_SourceProof_c1f3beb58834c65ab1c84683
-- name    : SourceProof_c1f3beb58834c65ab1c84683
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:02:03.787899+00:00
-- url     : https://prove2.me/theorems/b9bde86b-d580-5312-8b5b-2287bd836374
-- title:
--   StochLean source theorem: ProbabilityTheory.eVariationOn_univ_stoppedProcess

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000
import Definitions.Def_SourceProof_407218b22ae1495f01bcf52b
import Definitions.Def_SourceProof_6229da19f14c641cf213eeef
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Tactic.Order
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Whole-half-line variation after stopping

The actual extended variation of a stopped path is its variation up to the
stopping time, including the stopping endpoint. Infinite times use the
original whole-half-line variation through the existing terminal-valued
sampling owner. None of these pathwise statements require stopping-time
measurability, cadlag paths, or finite variation.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_c1f3beb58834c65ab1c84683 (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ =
      stoppedValueWithTerminal (eTotalVariationProcess X)
        (fun ω ↦ eVariationOn (X · ω) univ) τ ω := by
  cases ht : τ ω with
  | top =>
      simp only [MeasureTheory.stoppedProcess, ht, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe, _root_.Prove2MeSourceProof.h_407218b22ae1495f01bcf52b ht]
  | coe T =>
      rw [_root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc (ht ▸ WithTop.coe_ne_top)]
      simp only [MeasureTheory.stoppedProcess, stoppedValue, ht, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe, ProbabilityTheory.eTotalVariationProcess]
      have him : (fun u : ℝ≥0 ↦ min u T) '' univ = Icc 0 T := by
        ext u
        constructor
        · rintro ⟨v, _, rfl⟩
          exact ⟨bot_le, min_le_right _ _⟩
        · intro hu
          exact ⟨u, mem_univ _, min_eq_left hu.2⟩
      exact (eVariationOn.comp_eq_of_monotoneOn (X · ω) (fun u ↦ min u T)
        (fun _ _ _ _ h ↦ min_le_min_right T h)).trans
        (congrArg (eVariationOn (X · ω)) him)
end ProbabilityTheory


