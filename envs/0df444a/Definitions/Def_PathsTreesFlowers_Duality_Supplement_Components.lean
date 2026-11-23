-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_Supplement_Components
-- name    : PathsTreesFlowers_Duality_Supplement_Components
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:33:47.167845+00:00
-- url     : https://prove2.me/theorems/63879d6f-a431-4e3c-bd72-161561040d72
-- title:
--   3.0–3.4 — edge-formed components and alternating circuits
-- statement:
--   Let $G$ be a finite loopless multigraph with distinct edge identities, and let $F$ be a set of edges. Its edge-formed graph has exactly the vertices meeting edges of $F$. A component is a nonempty connected subgraph with vertices among these endpoints, containing all $F$-edges internal to it, and closed under following any incident $F$-edge. Thus there are no extra isolated ambient vertices.
--
--   For a circuit with cyclically ordered edges $e_0,\ldots,e_{m-1}$, alternation with respect to a matching $M$ means
--   $$e_i\in M\quad\Longleftrightarrow\quad e_{(i+1)\bmod m}\notin M\qquad(0\le i<m).$$
--
--   These objects express the full component decomposition of the symmetric difference of two matchings. The underlying subgraphs, paths and circuits are the published base objects; parallel edges remain distinct.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 452–453, 3.0–3.4

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §3.1: exactly the endpoints of an edge set, with no ambient isolated vertices. -/
def edgeVertices (G : EdmondsMatching65.Polyhedron.Graph V E) (F : Finset E) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ F, v ∈ G.ends e)

/-- §3.0: a whole connected component of the graph formed by F. -/
def IsEdgeComponent (G : EdmondsMatching65.Polyhedron.Graph V E) (F : Finset E)
    (C : Sub G) : Prop :=
  IsConnectedSub G C ∧ C.verts ⊆ edgeVertices G F ∧
    C.edges = F.filter (fun e => G.ends e ∈ C.verts.sym2) ∧
    ∀ e ∈ F, ∀ u ∈ C.verts, u ∈ G.ends e → ∀ v ∈ G.ends e, v ∈ C.verts

/-- §3.4: alternation also holds across the last/first edge of a circuit. -/
def IsAlternatingCircuit (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (vs : List V) (es : List E) : Prop :=
  IsCircuit G vs es ∧
    ∀ ef ∈ es.zip (es.rotate 1), (ef.1 ∈ M ↔ ef.2 ∉ M)

end PathsTreesFlowers.Duality.Supplement


