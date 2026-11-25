-- Prove2me | Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
-- name    : SourceProof_60fbb0806e5cb393cb74e054
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:32:57.811528+00:00
-- url     : https://prove2.me/theorems/f711d2b3-9b10-5abc-bbbd-c003281abbeb
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_const

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c4820ee40112f49cbc123f5f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 {ι : Type*} (l : Filter ι) (Y : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun _ : ι ↦ Y) l Y := by
  intro T ε hε
  simpa [not_le_of_gt hε] using
    (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
end ProbabilityTheory


