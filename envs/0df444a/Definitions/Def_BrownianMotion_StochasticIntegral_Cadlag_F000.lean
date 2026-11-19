-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F000
-- name    : BrownianMotion_StochasticIntegral_Cadlag_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:09:12.377965+00:00
-- url     : https://prove2.me/theorems/0486ea6d-238f-46b5-9a2c-10d8ae6f8903
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Cadlag
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.StochasticIntegral.Cadlag, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-! # cadlag functions

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

/-- The predicate that a function is right continuous. -/
abbrev Function.IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a
lemma Function.IsRightContinuous.continuous_comp {F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [Preorder ι] {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : IsRightContinuous f) : IsRightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)
@[simp]
lemma Function.isRightContinuous_const [TopologicalSpace E] [Preorder ι] (c : E) :
    IsRightContinuous (fun _ ↦ c : ι → E) :=
  fun _ ↦ continuousWithinAt_const
/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [TopologicalSpace E] [Preorder ι] (f : ι → E) : Prop where
  right_continuous : Function.IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)
@[simp]
lemma isCadlag_const [TopologicalSpace E] [Preorder ι] (c : E) : IsCadlag (fun _ ↦ c : ι → E) :=
  ⟨Function.isRightContinuous_const c, fun _ ↦ ⟨c, tendsto_const_nhds⟩⟩
lemma Continuous.isCadlag [TopologicalSpace E] [Preorder ι] {f : ι → E} (hf : Continuous f) :
    IsCadlag f :=
  ⟨fun _ ↦ hf.continuousWithinAt, fun x ↦ ⟨f x, hf.continuousAt.continuousWithinAt⟩⟩
section Jump

/-- The set of left jump times of a function. -/
def leftJumpSet [TopologicalSpace E] [LinearOrder ι] (f : ι → E) : Set ι :=
  {t | f.leftLim t ≠ f t}
/-- For a càdlàg function, the left jump times are exactly its discontinuity points. -/
theorem IsCadlag.leftJumpSet_eq_discontinuitySet [LinearOrder ι] [OrderTopology ι]
    [TopologicalSpace E] [T2Space E] {f : ι → E} (hf : IsCadlag f) :
    leftJumpSet f = {t | ¬ ContinuousAt f t} := by
  ext t
  refine ⟨fun h hc => h (hc.continuousWithinAt.leftLim_eq), fun hc h => hc ?_⟩
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, hf.right_continuous t⟩
  simpa [ContinuousWithinAt, h] using tendsto_leftLim_of_tendsto (hf.left_limit t)
/-- The set of large left jump times. -/
def largeLeftJumpSet [TopologicalSpace E] [LinearOrder ι] (f : ι → E)
    (v : Set (E × E)) : Set ι :=
  {t | ⟨f t, f.leftLim t⟩ ∉ v}
end Jump


