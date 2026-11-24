-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
-- name    : StochLean_Probability_Process_Path_FiniteVariation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:01.172615+00:00
-- url     : https://prove2.me/theorems/8009f92b-1f24-477d-b461-b8b26007276d
-- title:
--   StochLean: Probability.Process.Path.FiniteVariation F000

import Definitions.Def_StochLean_Probability_Process_Path_Monotone_F000
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite variation on one common path event

The deterministic owners remain Mathlib's bounded and locally bounded variation.
Local finite variation and finite total variation on the half-line are distinct.
Cadlag paths and adaptedness are separate hypotheses, not implicit fields.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def HasFiniteVariationPaths (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t ↦ X t ω) univ
def HasFiniteTotalVariationPaths (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, BoundedVariationOn (fun t ↦ X t ω) univ
variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end ProbabilityTheory


