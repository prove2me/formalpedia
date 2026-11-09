-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg
-- name    : HybridXorLift_ParallelHybridAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:38.2292+00:00
-- url     : https://prove2.me/theorems/7b05b164-2191-4e32-a426-2138aeb1ea21
-- title:
--   Parallel hybrid algorithm
-- statement:
--   A **parallel hybrid algorithm** is a finite classical decision tree whose internal nodes run parallel subroutines and whose leaves carry outputs; the complete measurement outcome $y$ of a subroutine selects the child. A **parallel $q$-query hybrid algorithm** is one in which every subroutine is parallel with at most $q$ slots.
--
--   **Formalization Note** Nodes with zero slots (no query) are allowed, as in the refined algorithm of §2.2 ("nodes that make no query may remain in the tree").
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.2, p.9 (PDF p.11); refinement of §2.2, p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_ParallelSub

namespace HybridXorLift

/-- A hybrid algorithm all of whose subroutines are parallel (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.2, p.9
(PDF p.11), refined as in §2.2, p.10 (PDF p.12)): a finite classical decision tree; an internal
node `round k w S next` runs the parallel subroutine `S` with `k` slots and moves to the child
`next y` selected by the complete measurement outcome `y`; a leaf `halt a` outputs `a`.
A parallel `q`-query hybrid algorithm is one with `SlotsAtMost q`.

**Formalization Note** Nodes with `k = 0` (no query) are allowed, as in the refined algorithm of
§2.2 ("nodes that make no query may remain in the tree"). -/
inductive ParallelHybridAlg (ι : Type) [Fintype ι] [DecidableEq ι] (α : Type) : Type where
  /-- a leaf with output `a` -/
  | halt (a : α)
  /-- an internal node running a parallel subroutine with `k` slots and workspace `Fin w` -/
  | round (k w : ℕ) (S : ParallelSub ι k w)
      (next : (Fin k → ι × Bool) × Fin w → ParallelHybridAlg ι α)

end HybridXorLift


