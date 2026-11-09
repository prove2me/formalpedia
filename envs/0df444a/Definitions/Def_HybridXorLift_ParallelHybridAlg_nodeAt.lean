-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_nodeAt
-- name    : HybridXorLift_ParallelHybridAlg_nodeAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:10.26595+00:00
-- url     : https://prove2.me/theorems/33e5caf9-a8c6-4ea0-a96f-e1583b7b47bf
-- title:
--   Node reached by a history
-- statement:
--   Following a history $h$ from the root of a parallel hybrid algorithm reaches a node of the tree, the subtree at the end of $h$. A history is **internal** when this node runs a subroutine and **terminal** when it is a leaf. A list of records that leaves the tree is not a history and reaches no node.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2 "Histories", p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_ParallelHybridAlg
import Definitions.Def_HybridXorLift_decodeStep

namespace HybridXorLift

/-- The node reached by a history (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2 "Histories", p.10 (PDF p.12)): `some N` for the
subtree `N` at the end of the path `h`, `none` when `h` is not a history. `h` is internal when
`N` is a `round` node and terminal when it is a `halt` leaf. -/
def ParallelHybridAlg.nodeAt {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} :
    ParallelHybridAlg ι α → List (Step ι) → Option (ParallelHybridAlg ι α)
  | A, [] => some A
  | .halt _, _ :: _ => none
  | .round k w _ next, u :: l =>
      match decodeStep k w u with
      | some y => (next y).nodeAt l
      | none => none

end HybridXorLift


