-- Prove2me | Definitions.Def_SourceProof_7270b3ab7a1632573e0ea3ed
-- name    : SourceProof_7270b3ab7a1632573e0ea3ed
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:35.989897+00:00
-- url     : https://prove2.me/theorems/f77437e9-cb66-49df-b42e-923255ee19fd
-- title:
--   StochLean source theorem: MeasureTheory.StronglyMeasurable.indicator_stoppingTime_le

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing stopped information at and after its stopping time

This is the source process used to prove Protter I.6. The coefficient is
measurable at the native stopped field, not prematurely at time zero. Its
activation path is cadlag, including zero and infinite lifetimes.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0} [TopologicalSpace E] [Zero E]

namespace StronglyMeasurable
theorem _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed (hτ : IsStoppingTime F τ)
    {Z : Ω → E} (hZ : StronglyMeasurable[hτ.measurableSpace] Z) (t : ℝ≥0) :
    StronglyMeasurable[F t] ({ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  have hm := hτ.measurableSet_le' t
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hm ?_
    (hZ.indicator hm) ?_
  · intro A hA
    have hs := hA.2 t
    convert hs using 1
    ext ω
    simp only [mem_inter_iff]
    tauto
  · intro ω hω
    exact Set.indicator_of_notMem hω _
end StronglyMeasurable

end MeasureTheory


