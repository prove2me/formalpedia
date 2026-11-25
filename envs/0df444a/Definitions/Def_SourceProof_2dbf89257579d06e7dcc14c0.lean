-- Prove2me | Definitions.Def_SourceProof_2dbf89257579d06e7dcc14c0
-- name    : SourceProof_2dbf89257579d06e7dcc14c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:14.313865+00:00
-- url     : https://prove2.me/theorems/9769ed99-a055-46c4-90bb-a6899e9e695b
-- title:
--   StochLean source theorem: tendsto_rightGrid

import Definitions.Def_SourceProof_5a9e4b64f838761a6226e9d1
import Definitions.Def_SourceProof_ab02c4076c4a85270a6dfe9e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

theorem _root_.Prove2MeSourceProof.h_2dbf89257579d06e7dcc14c0 (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ rightGrid n t) Filter.atTop (𝓝 t) := by
  have hu : Filter.Tendsto (fun n : ℕ ↦ t + 1 / ((n : ℝ≥0) + 1))
      Filter.atTop (𝓝 t) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1))
            Filter.atTop (𝓝 0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n ↦ _root_.Prove2MeSourceProof.h_5a9e4b64f838761a6226e9d1 n t) (fun n ↦ by
      simpa [Nat.cast_add, Nat.cast_one] using (_root_.Prove2MeSourceProof.h_ab02c4076c4a85270a6dfe9e n t).le)
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


