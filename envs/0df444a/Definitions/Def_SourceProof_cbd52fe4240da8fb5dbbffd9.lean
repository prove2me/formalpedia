-- Prove2me | Definitions.Def_SourceProof_cbd52fe4240da8fb5dbbffd9
-- name    : SourceProof_cbd52fe4240da8fb5dbbffd9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:00:55.702241+00:00
-- url     : https://prove2.me/theorems/53db1b17-5107-552b-a935-19562022fc73
-- title:
--   StochLean source theorem: StochLean.TimePartition.tendsto_sum_endpointPairStep_of_cadlag

import Definitions.Def_SourceProof_5d91e4514b2045211b63e301

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-pair sums on finitely selected cells

A selected time belongs to a left-open, right-closed cell. Once no two
selected times share a cell, the sum over selected times equals exactly
the sum over selected cells. The limit retains both sides of every jump.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean.TimePartition

theorem _root_.Prove2MeSourceProof.h_cbd52fe4240da8fb5dbbffd9 {E : Type*} [MetricSpace E] {T : ℝ≥0}
    {π : ℕ → TimePartition T} (A : Finset ℝ≥0) (hA : ∀ s ∈ A, s ∈ Ioc 0 T)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ s ∈ A, (π n).endpointPairStep Φ x s) atTop
      (𝓝 (∑ s ∈ A, Φ (Function.leftLim x s) (x s))) := by
  apply tendsto_finsetSum
  intro s hs
  exact _root_.Prove2MeSourceProof.h_5d91e4514b2045211b63e301 hΦ hx (hA s hs) hmesh
end StochLean.TimePartition


