-- Prove2me | Definitions.Def_SourceProof_a76267fbd246c80475c88941
-- name    : SourceProof_a76267fbd246c80475c88941
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:28:38.82586+00:00
-- url     : https://prove2.me/theorems/2bb937e1-0924-4466-9a29-d38d446d291f
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.leftSampleProcess_zero

import Definitions.Def_SourceProof_2b513c204954b4445bde4e1f
import Definitions.Def_SourceProof_319b7c355ab18ac90eeaae81

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left sampling is a compact-deviation contraction

The bound is uniform over arbitrary random partitions and requires no path
regularity or measurability. It does not assert that sampling a discontinuous
path on finer partitions converges uniformly to its left-limit process.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {l : Filter ι} {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_a76267fbd246c80475c88941 {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l 0) (π : ι → StoppingTimePartition F) :
    TendstoUCP P (fun n ↦ (π n).leftSampleProcess (Z n)) l 0 := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  intro ω hω
  change ε ≤ ProbabilityTheory.compactDeviation ((π n).leftSampleProcess (Z n)) 0 T ω at hω
  change ε ≤ ProbabilityTheory.compactDeviation (Z n) 0 T ω
  apply hω.trans
  simpa only [_root_.Prove2MeSourceProof.h_2b513c204954b4445bde4e1f] using
    (_root_.Prove2MeSourceProof.h_319b7c355ab18ac90eeaae81 (X := Z n) (Y := 0) (π n) T ω)
end TendstoUCP

end ProbabilityTheory


