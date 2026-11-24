-- Prove2me | Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
-- name    : SourceProof_264b430747bbe6ee020dbafc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:40.855567+00:00
-- url     : https://prove2.me/theorems/51651a0f-e7bd-4a32-833e-9353d474b830
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.continuous_comp

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_60b56e0d38c6166660de298f
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

variable [OrderBot T]

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (hX : HasCadlagPaths X P)
    {f : E → G} (hf : Continuous f) : HasCadlagPaths (fun t ω ↦ f (X t ω)) P :=
  hX.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f hω) hf
end HasCadlagPaths

end ProbabilityTheory


