-- Prove2me | Definitions.Def_PathsTreesFlowers_Invariance_Shrink
-- name    : PathsTreesFlowers_Invariance_Shrink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:26.768017+00:00
-- url     : https://prove2.me/theorems/91487113-8744-4a1f-8a33-576290018f38
-- title:
--   4.5, 4.9–4.11, pp. 455–458 — shrinking a partition into pseudovertices, M/P, blossom sets and odd-circuit sets (nested shrinking)
-- statement:
--   Let $G$ be a finite graph and $M$ a set of edges. This file encodes Edmonds' *shrinking* of subgraphs into *pseudovertices* (4.9–4.11), including shrinking nested blossoms.
--
--   1. **Shrinking a partition** (4.9, 4.11). Let $\mathcal P$ be a partition of the vertex set $V$ into nonempty parts. The graph $G/\mathcal P$ has the parts of $\mathcal P$ as its vertices. Its edges are the edges of $G$ whose two end-points lie in different parts; each keeps its identity, and its end-points in $G/\mathcal P$ are the parts containing its end-points in $G$. Edges with both end-points in one part disappear. A part $U$ with more than one vertex is a *pseudovertex* of $G/\mathcal P$, and $U^+$ is its *complete expansion* (4.11). Shrinking a single connected set $U$ ($G/U$) is the case where all other parts are single vertices; several disjoint sets are shrunk at once.
--   2. **$M/\mathcal P$** (4.10). $M/\mathcal P = M \cap (G/\mathcal P)$ is the set of edges of $M$ that survive in $G/\mathcal P$.
--   3. **Blossom sets** (4.5, 4.10, 4.11). Every single vertex $\{v\}$ is a blossom set for $M$. If $U_0, \dots, U_{2k}$ with $k \ge 1$ are pairwise disjoint blossom sets for $M$ and $e_0, \dots, e_{2k}$ are edges of $G$ such that $e_i$ joins a vertex of $U_i$ to a vertex of $U_{i+1}$ (indices mod $2k+1$) and
--   $$e_i \in M \iff i \text{ is odd},$$
--   then $U_0 \cup \dots \cup U_{2k}$ is a blossom set for $M$. In the graph in which the $U_i$ have been shrunk, the $e_i$ form an odd circuit $B$ for which $M \cap B$ is a maximum matching of $B$ leaving $U_0$ exposed, i.e. a *blossom* (4.5); so blossom sets are exactly the complete expansions of pseudovertices obtained by successively shrinking blossoms.
--   4. **Odd-circuit sets** (4.10, 4.11, 4.14). The same induction without the condition on $M$: the complete expansions of pseudovertices obtained by successively shrinking arbitrary odd circuits.
--
--   Shrinking is the operation that turns Edmonds' alternating-tree search into an algorithm, and the graph $G^*$ of Section 6 is a shrinking of $G$ along blossom sets.
--
--   **Formalization Note** The shrunken graph is the contraction of $G$ along a `Finpartition` of the vertex set: its vertex type is the type of parts and its edge type is the subtype of surviving edges, so there are no spurious isolated vertices. The paper shrinks one odd circuit at a time ($G_i = G_{i-1}/B_i$); the inductive predicates record the nested circuits directly, as sets of vertices of $G$. Because the $U_i$ are disjoint and $2k+1 \ge 3$, the $e_i$ are distinct edges of the current graph and form a circuit. The paper defines shrinking for connected $H$ (4.9); blossom and odd-circuit sets are connected by construction, and the one statement that shrinks other sets (4.15, extension) assumes connectedness explicitly.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 455, 4.5; pp. 456–458, 4.9, 4.10, 4.11 (pseudovertices, complete expansion)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The vertex of the shrunken graph to which the vertex `v` of `G` is sent: its part
`P.part v` of the partition `P`. -/
def partOf (P : Finpartition (Finset.univ : Finset V)) (v : V) : {U : Finset V // U ∈ P.parts} :=
  ⟨P.part v, P.part_mem.2 (Finset.mem_univ v)⟩

/-- The edges of `G` that survive shrinking the parts of `P`: those whose two end-points lie in
different parts. -/
abbrev ShrinkE (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) : Type :=
  {e : E // ¬ ((G.ends e).map (partOf P)).IsDiag}

/-- *Shrinking* (4.9–4.11, pp. 456–457) every part of the partition `P` of the vertices of `G` at
once. The vertices of `shrink G P` are the parts of `P` (a part with more than one vertex is a
pseudovertex, and the part is its complete expansion); its edges are the edges of `G` joining two
different parts, which keep their identity; an edge's end-points are the parts containing its
end-points in `G`. Edges with both end-points in one part disappear. Shrinking a single vertex set
`U` is the case where every other part is a singleton. -/
def shrink (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) :
    EdmondsMatching65.Polyhedron.Graph {U : Finset V // U ∈ P.parts} (ShrinkE G P) where
  ends e := (G.ends e.1).map (partOf P)
  loopless e := e.2

/-- `M/P = M ∩ (G/P)` (4.10, p. 457): the edges of `M` that survive in the shrunken graph. -/
def shrinkMatching (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P : Finpartition (Finset.univ : Finset V)) (M : Finset E) : Finset (ShrinkE G P) :=
  M.subtype _

/-- *Odd-circuit sets* (4.10, 4.11, 4.14, pp. 457–458): the complete expansions of pseudovertices
obtained by successively shrinking arbitrary odd circuits. The same induction as `IsBlossomSet`
without any condition on a matching. -/
inductive IsOddCircuitSet (G : EdmondsMatching65.Polyhedron.Graph V E) : Finset V → Prop
  | singleton (v : V) : IsOddCircuitSet G {v}
  | circuit (k : ℕ) (hk : 1 ≤ k) (U : Fin (2 * k + 1) → Finset V) (e : Fin (2 * k + 1) → E)
      (hU : ∀ i, IsOddCircuitSet G (U i))
      (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
      (hends : ∀ i, ∃ a ∈ U i, ∃ b ∈ U (i + 1), G.ends (e i) = s(a, b)) :
      IsOddCircuitSet G (Finset.univ.biUnion U)

end PathsTreesFlowers.Invariance


