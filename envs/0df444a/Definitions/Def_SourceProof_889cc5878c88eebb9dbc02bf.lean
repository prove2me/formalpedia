-- Prove2me | Definitions.Def_SourceProof_889cc5878c88eebb9dbc02bf
-- name    : SourceProof_889cc5878c88eebb9dbc02bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:33.919503+00:00
-- url     : https://prove2.me/theorems/eab840a0-2350-4346-907b-1b1f664bd351
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.pi

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_2904b8e06bc36e3ab7c34bfd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag coordinate products and their actual left limits

The deterministic product property holds for arbitrary index types. The
common-event stochastic assertion requires countably many coordinates.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ProbabilityTheory

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf {T Ω ι : Type*} [LinearOrder T] [TopologicalSpace T] [OrderBot T]
    {mΩ : MeasurableSpace Ω} {E : ι → Type*} [∀ i, TopologicalSpace (E i)] [Countable ι]
    {X : (i : ι) → T → Ω → E i} {P : Measure Ω} (hX : ∀ i, HasCadlagPaths (X i) P) :
    HasCadlagPaths (fun t ω i ↦ X i t ω) P := by
  have h : ∀ᵐ ω ∂P, ∀ i, ProbabilityTheory.IsCadlagPath (X i · ω) := ae_all_iff.mpr hX
  exact h.mono fun _ hω ↦ _root_.Prove2MeSourceProof.h_2904b8e06bc36e3ab7c34bfd.mpr hω
end HasCadlagPaths

end ProbabilityTheory


