-- Prove2me | Definitions.Def_EdmondsPartition_Main_Graphic
-- name    : EdmondsPartition_Main_Graphic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:51:51.61731+00:00
-- url     : https://prove2.me/theorems/2e1b9448-a40f-4a70-a0de-a0156cb238d6
-- title:
--   §1.0, §1.1, §1.7, pp. 67–71 — the incidence matrix N(G) mod 2, the graphic independent sets, and E_U
-- statement:
--   Let $G$ be a finite graph with node set $V$ and edge set $E$, each edge having two distinct ends; parallel edges are allowed. Following Edmonds, $G$ is regarded as its node–edge incidence matrix $N(G)$ over the integers mod 2: the rows are the nodes, the columns are the edges, and the column of edge $e$ has a one in the row of each of its two ends and zeroes elsewhere.
--
--   1. **Graphic independence** (the third example of §1.1). A set $F$ of edges is independent when the columns of $N(G)$ indexed by $F$ are linearly independent over $\mathbb Z/2\mathbb Z$.
--   2. **Induced edge sets** (§1.7). For a set $U$ of nodes, $E_U$ is the set of edges of $G$ with both ends in $U$.
--
--   These are the objects of the Nash-Williams COROLLARY: its "circuits of $G$" are the circuits of this matroid.
--
--   **Formalization Note** The graph is the published `EdmondsMatching65.Polyhedron.Graph`: a map from edges to unordered pairs of nodes, with no loops (each column has exactly two ones) and parallel edges allowed. Independence is linear independence of the family of incidence columns `V → ZMod 2` indexed by the elements of `F`.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 67 (§1.0, matrix N(G)), p. 68 (§1.1, third example), p. 71 (§1.7, E_U)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsPartition.Main

variable {V E : Type*} [DecidableEq V]

/-- §1.0, p. 67: the column of edge `e` in the node–edge incidence matrix `N(G)` over the
integers mod 2: a one in the row of each of the two ends of `e`, zeroes elsewhere. -/
def incidenceColumn (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) : V → ZMod 2 :=
  fun v => if v ∈ G.ends e then 1 else 0

/-- §1.1, p. 68 (third example): a set `F` of edges of `G` is independent when its edges,
as column vectors of `N(G)` over the integers mod 2, are linearly independent. -/
def graphicIndep (G : EdmondsMatching65.Polyhedron.Graph V E) (F : Finset E) : Prop :=
  LinearIndependent (ZMod 2) (fun e : F => incidenceColumn G (e : E))

open Classical in
/-- §1.7, p. 71: `E_U`, the set of edges of `G` which have both ends in the node set `U`. -/
noncomputable def edgesWithin [Fintype E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (U : Finset V) : Finset E :=
  Finset.univ.filter (fun e => ∀ v ∈ G.ends e, v ∈ U)

end EdmondsPartition.Main


