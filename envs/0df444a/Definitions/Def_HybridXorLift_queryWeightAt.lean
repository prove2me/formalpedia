-- Prove2me | Definitions.Def_HybridXorLift_queryWeightAt
-- name    : HybridXorLift_queryWeightAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:17.065636+00:00
-- url     : https://prove2.me/theorems/ec334d02-0670-4a5d-add5-bc2eb3c76a9f
-- title:
--   Query weight $\beta_i(h)$ at a history
-- statement:
--   For an internal history $h$, $\beta_i(h)$ is the query weight of block $i$ in the subroutine run at $h$. A terminal history runs no subroutine and gets weight $0$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.1, Eq. (4.1), p.14 (PDF p.16)

import Definitions.Def_HybridXorLift_ParallelSub_queryWeight
import Definitions.Def_HybridXorLift_ParallelHybridAlg_nodeAt

namespace HybridXorLift

/-- The query weight `β_i(h)` of block `i` at a history `h` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.1, Eq. (4.1), p.14
(PDF p.16)): the query weight of the subroutine at `h` when `h` is internal, and `0` otherwise
(a terminal history runs no subroutine). -/
noncomputable def queryWeightAt {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) (i : Fin n) : ℝ :=
  match A.nodeAt h with
  | some (.round _ _ S _) => S.queryWeight i
  | _ => 0

end HybridXorLift


