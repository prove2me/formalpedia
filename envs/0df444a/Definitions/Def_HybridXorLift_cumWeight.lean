-- Prove2me | Definitions.Def_HybridXorLift_cumWeight
-- name    : HybridXorLift_cumWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:18.090022+00:00
-- url     : https://prove2.me/theorems/bb75598c-f573-447d-a003-3b9d9c2be8a6
-- title:
--   Cumulative weight $w_i(h)$
-- statement:
--   For a history $h$ and a block $i$, the **cumulative weight** is
--   $$
--   w_i(h) = \sum_{v \prec h} \beta_i(v),
--   $$
--   the total query weight placed on block $i$ by the subroutines at the strict ancestors of $h$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, Eq. (4.8), p.15 (PDF p.17)

import Definitions.Def_HybridXorLift_queryWeightAt

namespace HybridXorLift

/-- The cumulative weight `w_i(h) = Σ_{v ≺ h} β_i(v)` of block `i` at history `h` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2,
Eq. (4.8), p.15 (PDF p.17)): the sum over the strict ancestors `v` of `h`, which are the proper
prefixes `h.take t`, `t < |h|`. -/
noncomputable def cumWeight {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.range h.length, queryWeightAt A (h.take t) i

end HybridXorLift


