-- Prove2me | Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
-- name    : StochLean_Probability_Process_Measurability_Optional_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:19:45.873933+00:00
-- url     : https://prove2.me/theorems/7e632549-58c2-4d19-b32e-a3178751b21c
-- title:
--   StochLean: Probability.Process.Measurability.Optional F001

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The optional sigma-field and the source inclusion chain

Protter III.1 defines the optional sigma-field using adapted cadlag real
processes. Everywhere path regularity is used in its generators. For merely
almost-sure cadlag paths the bridge constructs an indistinguishable optional
version; it does not assert optionality of arbitrary exceptional trajectories.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Filtration

end Filtration

namespace Filtration

end Filtration

variable {E : Type*} [TopologicalSpace E] {F : Filtration ℝ≥0 mΩ}

/-- Strong optional measurability; for real processes this is ordinary optional measurability. -/
def IsStronglyOptional (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → E) : Prop :=
  StronglyMeasurable[F.optional] (Function.uncurry X)
end MeasureTheory


