-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_Jordan_F000
-- name    : StochLean_Probability_Process_FiniteVariation_Jordan_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:01:49.282503+00:00
-- url     : https://prove2.me/theorems/6183d79a-5971-5071-8273-d3e94e40194b
-- title:
--   StochLean: Probability.Process.FiniteVariation.Jordan F000

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Canonical increasing components of a finite-variation process

Both components start at zero. They decompose increments, with the initial
random variable kept separate. No integrability of the variation is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def positiveVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathPositiveVariation (fun s ↦ X s ω) t
noncomputable def negativeVariationProcess (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathNegativeVariation (fun s ↦ X s ω) t
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

end MeasureTheory


