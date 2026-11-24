-- Prove2me | Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
-- name    : SourceProof_4a90e1998d81dac996f193f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:37.072848+00:00
-- url     : https://prove2.me/theorems/c08f90a0-eb7a-4c3c-b3d1-1cd78fd82f0d
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurableSpace_le

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Everywhere finite stopping times

These are witness data for Protter simple predictable representations, not a
replacement for Mathlib's `IsStoppingTime`. A source endpoint is finite at every
sample, which is stronger than almost-sure finiteness. Evaluation is ordinary
function application and never uses the totalized value at infinity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 (τ : FiniteStoppingTime F) : τ.measurableSpace ≤ mΩ :=
  τ.isStoppingTime.measurableSpace_le
end FiniteStoppingTime
end ProbabilityTheory


