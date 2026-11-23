-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_Supplement_Paths
-- name    : PathsTreesFlowers_Duality_Supplement_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:34:19.119799+00:00
-- url     : https://prove2.me/theorems/7bb4f01e-76b6-4e77-84b7-3793d2b55e5a
-- title:
--   3.3 and 4.3 — paths in a subgraph, contiguous subpaths and matching endpoints
-- statement:
--   Let $H$ be a subgraph of a finite loopless multigraph $G$. An oriented path in $H$ from $a$ to $b$ is a published simple path whose vertices and edges belong to $H$, with first vertex $a$ and last vertex $b$.
--
--   A path $(v,e)$ is a subpath of $(w,f)$ when, for some starting position $i$, its vertex and edge lists are the corresponding contiguous segments, possibly after reversing both lists:
--   $$v=w[i:i+|v|],\qquad e=f[i:i+|e|].$$
--
--   A matching endpoint is an endpoint with an incident end-edge in the matching. This requires a nonempty edge list. Root paths may have zero edges. These conventions retain the paper's subgraph paths up to orientation and give the precise meaning of the subpath conclusion of 4.3.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 453, 455, 3.3 and 4.3

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A source path inside a specified subgraph, oriented from a to b. -/
def PathIn (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G)
    (a b : V) (vs : List V) (es : List E) : Prop :=
  IsPath G vs es ∧ vs.toFinset ⊆ H.verts ∧ es.toFinset ⊆ H.edges ∧
    vs.head? = some a ∧ vs.getLast? = some b

/-- A contiguous vertex-and-edge segment, allowing reversal of the smaller path. -/
def IsSubpath (vs : List V) (es : List E) (ws : List V) (fs : List E) : Prop :=
  ∃ i : ℕ, (vs = (ws.drop i).take vs.length ∧ es = (fs.drop i).take es.length) ∨
    (vs.reverse = (ws.drop i).take vs.length ∧ es.reverse = (fs.drop i).take es.length)

/-- A positive-length path has a matching end-edge at its endpoint v. -/
def MatchingEnd (M : Finset E) (v : V) (vs : List V) (es : List E) : Prop :=
  (vs.head? = some v ∧ ∃ e, es.head? = some e ∧ e ∈ M) ∨
    (vs.getLast? = some v ∧ ∃ e, es.getLast? = some e ∧ e ∈ M)

end PathsTreesFlowers.Duality.Supplement


