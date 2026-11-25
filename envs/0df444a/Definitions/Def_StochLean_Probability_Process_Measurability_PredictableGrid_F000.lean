-- Prove2me | Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
-- name    : StochLean_Probability_Process_Measurability_PredictableGrid_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:34:42.826256+00:00
-- url     : https://prove2.me/theorems/ee066878-6cfa-4ade-b343-6699f76eb2d5
-- title:
--   StochLean: Probability.Process.Measurability.PredictableGrid F000

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
import Mathlib.Probability.Process.Predictable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

noncomputable def strictLeftGrid (δ t : ℝ≥0) : ℝ≥0 :=
  δ * ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0)
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


