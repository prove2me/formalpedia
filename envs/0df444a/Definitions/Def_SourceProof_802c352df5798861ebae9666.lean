-- Prove2me | Definitions.Def_SourceProof_802c352df5798861ebae9666
-- name    : SourceProof_802c352df5798861ebae9666
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:30.169781+00:00
-- url     : https://prove2.me/theorems/793c32ef-b180-4dbe-9727-d256802ac727
-- title:
--   StochLean source theorem: StochLean.tprod_Ioc_cutoff_le

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # One-sided regularity of locally absolutely convergent cumulative products

Closed positive-time products include the jump at the current time; their
strict-left limits are the products on the corresponding open interval.
Zero and negative factors are permitted. Dominated convergence is applied
to deviations from one, not to logarithms of possibly nonpositive factors.
-/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_802c352df5798861ebae9666 (f : ℝ≥0 → ℝ) (a t : ℝ≥0) :
    (∏' s : Ioc 0 t, (if (s : ℝ≥0) ≤ a then f s else 1)) =
      ∏' s : Ioc 0 (min t a), f s := by
  classical
  rw [tprod_subtype (Ioc 0 t) (fun s ↦ if s ≤ a then f s else 1),
    tprod_subtype (Ioc 0 (min t a)) f]
  apply tprod_congr
  intro s
  by_cases hs0 : 0 < s <;> by_cases hst : s ≤ t <;> by_cases hsa : s ≤ a <;>
    simp only [Set.mulIndicator, mem_Ioc, le_min_iff, hs0, hst, hsa,
      and_true, and_false, if_true, if_false]
end StochLean


