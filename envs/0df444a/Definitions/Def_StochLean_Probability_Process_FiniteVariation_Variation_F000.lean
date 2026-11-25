-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000
-- name    : StochLean_Probability_Process_FiniteVariation_Variation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:03.738883+00:00
-- url     : https://prove2.me/theorems/0fdc9756-a5fe-542f-ba5b-3cc2d4242241
-- title:
--   StochLean: Probability.Process.FiniteVariation.Variation F000

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_StochLean_Analysis_PathVariation_TotalVariation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def eTotalVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  eVariationOn (fun s ↦ X s ω) (Icc 0 t)
noncomputable def totalVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathTotalVariation (fun s ↦ X s ω) t
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end MeasureTheory


