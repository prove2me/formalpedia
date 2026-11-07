-- Prove2me | Definitions.Def_VDCyclePack_IsCycleList
-- name    : VDCyclePack_IsCycleList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:10:29.294189+00:00
-- url     : https://prove2.me/theorems/bbbfb920-3476-4b1c-8a23-4382bb5d1543
-- title:
--   A vertex list is a cycle of an encoded graph
-- statement:
--   A list of vertex indices is a **cycle list** if it represents some cycle of the encoded graph. Its entries are the vertex set of that cycle, so two cycle lists describe vertex-disjoint cycles exactly when they have no common entry.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_VDCyclePack_Represents

namespace VDCyclePack

/-- **A vertex list is a cycle of an encoded graph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3 ("returns a family P of pairwise vertex-disjoint cycles").

`IsCycleList I l` says `l` represents some cycle of `I.toGraph` (`Represents`). Its vertex set is the
set of entries of `l`, so two such lists describe vertex-disjoint cycles exactly when they are
disjoint as lists. -/
def IsCycleList (I : GraphInst) (l : List ℕ) : Prop :=
  ∃ C : I.toGraph.Subgraph, Represents I l C

end VDCyclePack


