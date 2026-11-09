-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_cost
-- name    : HybridXorLift_ParallelHybridAlg_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:50.301517+00:00
-- url     : https://prove2.me/theorems/bb9f06be-7065-4697-b4c2-ec93115f7be6
-- title:
--   Cost of a parallel hybrid algorithm
-- statement:
--   The **cost** of a parallel hybrid algorithm is the largest total number of oracle calls along a root-to-leaf path, where a subroutine with $k$ slots makes $k$ calls:
--   $$
--   \mathrm{cost}(\text{leaf}) = 0, \qquad \mathrm{cost}(\text{node with } k \text{ slots}) = k + \max_y \mathrm{cost}(A_y),
--   $$
--   the maximum ranging over all children.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_ParallelHybridAlg

namespace HybridXorLift

/-- The cost of a parallel hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1, p.9 (PDF p.11)): the largest
total number of oracle calls (a subroutine with `k` slots makes `k` calls) along a root-to-leaf
path, over all root-to-leaf paths. -/
def ParallelHybridAlg.cost {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} :
    ParallelHybridAlg ι α → ℕ
  | .halt _ => 0
  | .round k _ _ next => k + Finset.univ.sup fun y => (next y).cost

end HybridXorLift


