-- Prove2me | Definitions.Def_SourceProof_90c5865c7cef0dcc41ef4e98
-- name    : SourceProof_90c5865c7cef0dcc41ef4e98
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.161799+00:00
-- url     : https://prove2.me/theorems/b5c21857-e496-4a1e-94d5-9d879ddb925e
-- title:
--   StochLean source theorem: MeasureTheory.StronglyMeasurable.indicator_eq_finite_stoppingTime

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

/-! # Transporting a coefficient on a finite stopping-time collision

Information known at one stopping time is known at a second stopping time on
their finite coincidence event. The target is the native stopped sigma-field,
not the before sigma-field. No predictability, usualness, measure finiteness,
or finite-lifetime assumption is needed; the coefficient is explicitly zero
when the original lifetime is infinite.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {σ Γ : Ω → WithTop ℝ≥0} [TopologicalSpace E] [Zero E]

namespace StronglyMeasurable

theorem _root_.Prove2MeSourceProof.h_90c5865c7cef0dcc41ef4e98
    (hσ : IsStoppingTime F σ) (hΓ : IsStoppingTime F Γ) {D : Ω → E}
    (hD : StronglyMeasurable[hσ.measurableSpace] D) :
    StronglyMeasurable[hΓ.measurableSpace]
      ({ω | σ ω = Γ ω ∧ σ ω ≠ ⊤}.indicator D) := by
  let A : Set Ω := {ω | σ ω = Γ ω ∧ σ ω ≠ ⊤}
  have hm : MeasurableSet[hσ.measurableSpace] A :=
    (hσ.measurableSet_eq_stopping_time hΓ).inter
      (hσ.measurable (measurableSet_singleton ⊤)).compl
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hm ?_
    (hD.indicator hm) (fun ω hω ↦ indicator_of_notMem hω D)
  intro S hS
  have ht := (IsStoppingTime.measurableSet_min_iff hσ hΓ _).mp
    (hσ.measurableSet_inter_le hΓ (A ∩ S) hS)
  have he : (A ∩ S) ∩ {ω | σ ω ≤ Γ ω} = A ∩ S := by
    apply inter_eq_left.mpr
    intro ω hω
    exact hω.1.1.le
  simpa only [he] using ht.2
end StronglyMeasurable

end MeasureTheory


