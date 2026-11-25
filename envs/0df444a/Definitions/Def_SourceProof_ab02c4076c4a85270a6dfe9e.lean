-- Prove2me | Definitions.Def_SourceProof_ab02c4076c4a85270a6dfe9e
-- name    : SourceProof_ab02c4076c4a85270a6dfe9e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:55.267533+00:00
-- url     : https://prove2.me/theorems/d1c68b27-4228-4870-ad72-c4121f5662fa
-- title:
--   StochLean source theorem: rightGrid_lt

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

theorem _root_.Prove2MeSourceProof.h_ab02c4076c4a85270a6dfe9e (n : ℕ) (t : ℝ≥0) :
    rightGrid n t < t + 1 / (n + 1 : ℕ) := by
  rw [rightGrid, div_lt_iff₀ (by positivity)]
  have h := Nat.ceil_lt_add_one (R := ℝ≥0)
    (a := ((n + 1 : ℕ) : ℝ≥0) * t) (by positivity)
  convert h using 1
  rw [add_mul, one_div, inv_mul_cancel₀]
  · ring
  · positivity
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


