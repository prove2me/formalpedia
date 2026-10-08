-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_OddSetCover
-- name    : PathsTreesFlowers_Duality_OddSetCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:57:11.274979+00:00
-- url     : https://prove2.me/theorems/fbc366ad-bb5b-4017-93e8-653797b7a003
-- title:
--   §5.6, p. 462 — odd sets, their capacities, covering of edges, odd-set covers
-- statement:
--   Let $G$ be a finite graph with vertex set $V$.
--
--   1. An **odd set** is a set of vertices with an odd number of elements: either a single vertex, or $2k+1$ vertices with $k = 1, 2, \dots$.
--   2. The **capacity** of a set consisting of one vertex is $1$; the capacity of a set of $2k+1$ vertices ($k \ge 1$) is $k$.
--   3. A set consisting of one vertex **covers** an edge $e$ if $e$ meets the vertex. A set of $2k+1$ vertices ($k \ge 1$) covers $e$ if both end-points of $e$ are in the set.
--   4. An **odd-set cover** of $G$ is a family $\mathcal S$ of odd sets of vertices such that every edge of $G$ is covered by a member of $\mathcal S$. Its **capacity-sum** is
--   $$\operatorname{cap}(\mathcal S) = \sum_{U \in \mathcal S} \operatorname{cap}(U).$$
--   5. A **minimum** odd-set cover is one whose capacity-sum is at most that of every odd-set cover of $G$.
--
--   A set of $2k+1$ vertices contains at most $k$ edges of any matching, and a single vertex meets at most one; this is why odd-set covers bound the size of matchings from above.
--
--   **Formalization Note** A family is a finite set of vertex sets, so a member is not repeated; repeating a member only adds capacity and does not change the minimum. The capacity is defined by the page's two cases: the uniform formula $(|U|-1)/2$ would give a singleton capacity $0$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 462, 5.6

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 5.6, p. 462: an *odd set* of vertices: a set with an odd number of vertices, i.e. either one
vertex or `2k + 1` vertices with `k = 1, 2, …`. The empty set is not odd. -/
def IsOddSet (U : Finset V) : Prop :=
  Odd U.card

/-- 5.6, p. 462: the *capacity* of an odd set: one for a set consisting of one vertex, and `k` for
a set of `2k + 1` vertices (`k = 1, 2, …`). -/
def capacity (U : Finset V) : ℕ :=
  if U.card = 1 then 1 else (U.card - 1) / 2

/-- 5.6, p. 462: when the odd set `U` *covers* the edge `e`. A set consisting of one vertex covers
`e` if `e` meets the vertex; a set of `2k + 1` vertices (`k ≥ 1`) covers `e` if both end-points of
`e` are in the set. -/
def Covers (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) (e : E) : Prop :=
  if U.card = 1 then (∃ v ∈ U, v ∈ G.ends e) else G.ends e ∈ U.sym2

instance (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) :
    DecidablePred (Covers G U) := fun e => by
  unfold Covers; infer_instance

/-- 5.6, p. 462: an *odd-set cover* of `G`: a family of odd sets of vertices such that each edge
of `G` is covered by a member of the family. -/
def IsOddSetCover (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset (Finset V)) : Prop :=
  (∀ U ∈ S, IsOddSet U) ∧ ∀ e : E, ∃ U ∈ S, Covers G U e

/-- The capacity-sum of a family of odd sets. -/
def capacitySum (S : Finset (Finset V)) : ℕ :=
  ∑ U ∈ S, capacity U

/-- An odd-set cover of minimum capacity-sum. -/
def IsMinOddSetCover (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset (Finset V)) :
    Prop :=
  IsOddSetCover G S ∧ ∀ T : Finset (Finset V), IsOddSetCover G T → capacitySum S ≤ capacitySum T

end PathsTreesFlowers.Duality


