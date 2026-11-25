-- Prove2me | Definitions.Def_SourceProof_cd97db615490c31aef685008
-- name    : SourceProof_cd97db615490c31aef685008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:23.663533+00:00
-- url     : https://prove2.me/theorems/d8ca867f-98e4-569b-91c6-e1edd356e7e9
-- title:
--   StochLean source theorem: measurable_rightGrid

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

theorem _root_.Prove2MeSourceProof.h_cd97db615490c31aef685008 (n : ℕ) : Measurable (rightGrid n) := by
  unfold rightGrid
  fun_prop
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


