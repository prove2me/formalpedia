-- Prove2me | Definitions.Def_LCPlanarSteiner_IsRegion
-- name    : LCPlanarSteiner_IsRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:18.386401+00:00
-- url     : https://prove2.me/theorems/edf10e4c-2a97-4853-80c3-8952b6afad1e
-- title:
--   Regions $R = (C, B, E_R)$
-- statement:
--   A **region** of a graph consists of disjoint vertex sets $C$ (interior) and $B$ (boundary) and a set $E_R$ of owned arcs, each of which is an arc of the graph with head in $C$ and tail in $B \cup C$. Owned paths may leave $B$ but never return to it.
--
--   Regions are the subproblems of the rooted separator recursion of §3.
--
--   **Formalization Note** The terminal set $T_R \subseteq C$ of the paper is not part of this predicate.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **A region `R = (C, B, E_R, T_R)`: interior, boundary and owned arcs.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.1, p.5: "A region R = (C, B, E_R, T_R) has disjoint interior and boundary sets, terminals
T_R ⊆ C, and owned edges with head in C and tail in B ∪ C. Owned paths may leave B but cannot return
to it."

`IsRegion G C B ER`: `C` and `B` are disjoint vertex sets and every owned arc (in `E_R`) is an arc of
`G` whose head is in `C` and whose tail is in `B ∪ C`.

**Formalization Note.** The terminal set `T_R ⊆ C` is not part of this predicate; statements that
need a terminal name it. -/
def IsRegion (G : Net) (C B ER : Finset ℕ) : Prop :=
  Disjoint C B ∧ ∀ e ∈ ER, e < G.arcs.length ∧ G.hd e ∈ C ∧ (G.tl e ∈ B ∨ G.tl e ∈ C)

end LCPlanarSteiner


