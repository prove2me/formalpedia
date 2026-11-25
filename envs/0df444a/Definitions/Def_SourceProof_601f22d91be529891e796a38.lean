-- Prove2me | Definitions.Def_SourceProof_601f22d91be529891e796a38
-- name    : SourceProof_601f22d91be529891e796a38
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:39:40.99799+00:00
-- url     : https://prove2.me/theorems/e8367e5b-a140-5c5f-8b0e-8f216119ec65
-- title:
--   StochLean source theorem: ProbabilityTheory.hittingAfter_norm_mono

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded masked cutoffs of adapted caglad processes

Open norm exits need not attain their target. Compact path bounds prove divergence
without an attainment claim. The closed cutoff remains bounded at a positive exit
by left continuity; the initial mask handles arbitrary initial values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_601f22d91be529891e796a38 : Monotone (fun a : ℝ ↦ hittingAfter H {x | a < ‖x‖} 0) := by
  intro a b hab
  exact hittingAfter_anti H 0 (fun _ hx ↦ hab.trans_lt hx)
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

end MeasureTheory


