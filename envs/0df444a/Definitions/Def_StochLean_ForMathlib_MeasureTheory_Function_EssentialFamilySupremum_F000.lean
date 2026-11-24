-- Prove2me | Definitions.Def_StochLean_ForMathlib_MeasureTheory_Function_EssentialFamilySupremum_F000
-- name    : StochLean_ForMathlib_MeasureTheory_Function_EssentialFamilySupremum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:41.237227+00:00
-- url     : https://prove2.me/theorems/bf00027f-4735-4ad7-a03e-b018871f4724
-- title:
--   StochLean: ForMathlib.MeasureTheory.Function.EssentialFamilySupremum F000

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.Bases

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable essential suprema of arbitrarily indexed families

The relation is specified before proving existence. It is an almost-sure upper bound of each
coordinate and is below every other almost-sure upper bound, including a nonmeasurable bound.
It is not the pointwise supremum over an uncountable family of chosen representatives.

For an s-finite measure, countable essential unions of strict threshold events select a
countable subfamily with the same essential supremum. For each fixed original index, only the
countable dense threshold family is intersected almost surely. The empty index type is allowed
and gives zero. No global representative selector is introduced.
-/

@[expose] public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- A measurable essential supremum of a family of extended nonnegative random variables.
The comparison function in the least-upper-bound property need not be measurable. -/
structure IsAEFamilySupremum (μ : Measure Ω) (f : ι → Ω → ℝ≥0∞)
    (W : Ω → ℝ≥0∞) : Prop where
  measurable : Measurable W
  le_ae : ∀ i : ι, f i ≤ᵐ[μ] W
  ae_le : ∀ g : Ω → ℝ≥0∞, (∀ i : ι, f i ≤ᵐ[μ] g) → W ≤ᵐ[μ] g
variable {μ : Measure Ω} {f g : ι → Ω → ℝ≥0∞} {W V : Ω → ℝ≥0∞}

end MeasureTheory


