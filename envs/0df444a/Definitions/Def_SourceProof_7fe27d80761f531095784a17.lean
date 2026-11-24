-- Prove2me | Definitions.Def_SourceProof_7fe27d80761f531095784a17
-- name    : SourceProof_7fe27d80761f531095784a17
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:55.415636+00:00
-- url     : https://prove2.me/theorems/59efb11d-1714-4778-a419-333cd455b765
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.continuous_comp

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_666dd1ca96d37833a039b8b0
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous operations on cadlag and caglad paths

The process statements intersect finitely many common full-measure events.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E G : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [TopologicalSpace G] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_7fe27d80761f531095784a17 (hX : HasCagladPaths X P)
    {f : E → G} (hf : Continuous f) : HasCagladPaths (fun t ω ↦ f (X t ω)) P :=
  hX.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_666dd1ca96d37833a039b8b0 hω) hf
end HasCagladPaths

variable [OrderBot T]

end ProbabilityTheory


