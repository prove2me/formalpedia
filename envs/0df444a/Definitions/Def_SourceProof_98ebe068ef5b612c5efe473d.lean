-- Prove2me | Definitions.Def_SourceProof_98ebe068ef5b612c5efe473d
-- name    : SourceProof_98ebe068ef5b612c5efe473d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:37:56.839592+00:00
-- url     : https://prove2.me/theorems/3e57bcbc-550b-4378-83e3-4b91a5e1ad9d
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.comp_nonexpansive

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_148ab0aeb6244a7b680bc127
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Nonexpansive scalar maps act continuously in UCP

The event comparison works for outer measures; no path measurability or
finite-measure premise is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_98ebe068ef5b612c5efe473d {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    TendstoUCP P (fun n t ω ↦ f (Z n t ω)) l (fun t ω ↦ f (Y t ω)) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  intro ω hω
  exact hω.trans (_root_.Prove2MeSourceProof.h_148ab0aeb6244a7b680bc127 hf T ω)
end TendstoUCP

end ProbabilityTheory


