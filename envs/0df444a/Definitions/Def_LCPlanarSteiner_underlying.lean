-- Prove2me | Definitions.Def_LCPlanarSteiner_underlying
-- name    : LCPlanarSteiner_underlying
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:28.573224+00:00
-- url     : https://prove2.me/theorems/519743c6-6b26-44b8-bc35-436853881795
-- title:
--   Simple underlying undirected graph of a set of arcs
-- statement:
--   For a set $S$ of arcs, the **underlying graph** of $S$ is the simple undirected graph on the vertices $\{0, \dots, n-1\}$ in which two distinct vertices are adjacent when some arc of $S$ joins them in either direction. Orientation, multiplicity and loops are dropped.
--
--   The input graph is planar when the underlying graph of all its arcs is planar, and a strict forest has treewidth at most $w$ when its underlying graph does.
--
--   **Formalization Note** All $n$ vertices are present; isolated vertices change neither planarity nor treewidth.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2 (planarity; simple underlying undirected support)

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **The simple underlying undirected graph of a set of arcs.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "simple underlying undirected
support of treewidth at most w"; "We assume G is planar."

`underlying G S` is the simple graph on the vertices `0, …, n − 1` in which `u ≠ v` are adjacent iff
some arc of `S` joins them, in either direction. Orientation, multiplicity and loops are dropped.

**Formalization Note.** The vertex type is `Fin G.n`: all vertices are present, isolated ones
included (they change neither planarity nor treewidth). Planarity of the input multidigraph is
planarity of `underlying G G.allArcs` (loops and parallel arcs can always be drawn). -/
def underlying (G : Net) (S : Finset ℕ) : SimpleGraph (Fin G.n) :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ S, e < G.arcs.length ∧ G.tl e = u.val ∧ G.hd e = v.val

end LCPlanarSteiner


