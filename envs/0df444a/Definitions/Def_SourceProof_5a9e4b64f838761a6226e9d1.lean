-- Prove2me | Definitions.Def_SourceProof_5a9e4b64f838761a6226e9d1
-- name    : SourceProof_5a9e4b64f838761a6226e9d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:36.878023+00:00
-- url     : https://prove2.me/theorems/70738d6e-0fd4-497d-9d14-f45af4efa4a5
-- title:
--   StochLean source theorem: le_rightGrid

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000

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

theorem _root_.Prove2MeSourceProof.h_5a9e4b64f838761a6226e9d1 (n : ℕ) (t : ℝ≥0) : t ≤ rightGrid n t := by
  rw [rightGrid, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using Nat.le_ceil (((n + 1 : ℕ) : ℝ≥0) * t)
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


