-- Prove2me | Definitions.Def_NashWilliams61_TreePacking_Graphs
-- name    : NashWilliams61_TreePacking_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:04.69098+00:00
-- url     : https://prove2.me/theorems/b8fbe9c7-d418-44ac-9935-283c85e31af4
-- title:
--   Spanning trees, crossing edges $E_P(G)$, $E_X$, $\Delta_G(X)$, admissible and critical partitions and graphs (pp. 445–446, 448)
-- statement:
--   Throughout, a **graph** $G$ is a finite unoriented multigraph in which every edge joins two distinct vertices; two vertices may be joined by several edges. It is given by a finite vertex set $V$, a finite edge set $E$, and for each edge $e$ the unordered pair of its end-vertices. A **subgraph** is a pair $(W, F)$ of a vertex set $W \subseteq V$ and an edge set $F \subseteq E$; the graph $G$ itself is $(V, E)$.
--
--   1. **Tree.** The subgraph $(W, T)$ is a *tree* if $W$ is non-empty, every edge of $T$ has both ends in $W$, $T$ contains no cycle (every edge of $T$ is a bridge of $T$; two parallel edges form a cycle), and any two vertices of $W$ are joined by a path using edges of $T$ only.
--   2. **Spanning tree.** $T$ is a *spanning tree* of the subgraph $(W, F)$ if $T \subseteq F$ and $(W, T)$ is a tree; a spanning tree of $G$ is a spanning tree of $(V, E)$.
--   3. **$k$ edge-disjoint spanning trees.** $G$ has $k$ edge-disjoint spanning trees if there are spanning trees $T_1, \dots, T_k$ of $G$ with $T_i \cap T_j = \emptyset$ for $i \neq j$.
--   4. **Crossing edges.** For a partition $P$ of $V$ (a set of non-empty disjoint subsets of $V$ whose union is $V$), $E_P(G)$ is the set of edges whose two ends lie in different members of $P$; parallel edges are counted separately in $|E_P(G)|$.
--   5. **Inner edges and $\Delta$.** For $X \subseteq V$, $E_X$ is the set of edges with both ends in $X$, $e_X = |E_X|$, and
--   $$\Delta_G(X) = k\,(|X| - 1) - e_X \in \mathbb Z .$$
--   6. **Admissible, critical.** A partition $P$ of $V$ is *admissible* if $|E_P(G)| \ge k(|P| - 1)$ (condition (1)) and *critical* if $|E_P(G)| = k(|P| - 1)$. The graph $G$ is *admissible* if every partition of $V$ is admissible, and *critical* if $|E| = k(|V| - 1)$.
--
--   These are the objects in which Theorem 1 and all the lemmas of the paper are stated.
--
--   **Formalization Note** The graph is the published encoding `NagamochiIbaraki.EdgeConn` (`ends : E → Sym2 V`, loops excluded by a hypothesis of each theorem), whose `IsForest` and `edgeGraph` are reused. Partitions are Mathlib `Finpartition (Finset.univ : Finset V)`. All counts that involve a subtraction ($\Delta_G$, condition (1), criticality) are computed in $\mathbb Z$. The paper's $X^*$ is the subgraph $(X, E_X)$ and needs no separate definition.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 445 (Definitions), p. 446 (Definitions: E_X, e_X, Δ_G(X)), p. 448 (Definitions: admissible, critical)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph

namespace NashWilliams61.TreePacking

/-! Finite multigraphs, spanning trees, crossing edges, `E_X`, `Δ_G(X)`, admissible and
critical partitions and graphs (Nash-Williams 1961, pp. 445–446 and p. 448).

A graph `G` is a node type `V`, an edge type `E` and `ends : E → Sym2 V` (the published
encoding `NagamochiIbaraki.EdgeConn`); parallel edges are distinct elements of `E` with the
same ends, and loops are excluded by the hypothesis `∀ e, ¬ (ends e).IsDiag` carried by the
theorems. A subgraph is a pair `(W, F)` of a vertex set `W : Finset V` and an edge set
`F : Finset E`; the graph `G` itself is `(univ, univ)`. -/

open NagamochiIbaraki.EdgeConn

variable {V E : Type*}

/-- The subgraph `(W, T)` is a tree: `W` is non-empty, every edge of `T` has both ends in `W`,
`T` has no cycle (`IsForest`: every edge of `T` is a bridge of `T`, so two parallel edges or
a loop are excluded), and every two vertices of `W` are joined by a path of `T`-edges. -/
def IsTreeOn [DecidableEq E] (ends : E → Sym2 V) (W : Finset V) (T : Finset E) : Prop :=
  W.Nonempty ∧ (∀ e ∈ T, ∀ v ∈ ends e, v ∈ W) ∧ IsForest ends T ∧
    ∀ u ∈ W, ∀ v ∈ W, (edgeGraph ends T).Reachable u v

/-- `T` is (the edge set of) a spanning tree of the subgraph `(W, F)`: `T ⊆ F` and `(W, T)` is
a tree. -/
def IsSpanningTreeOn [DecidableEq E] (ends : E → Sym2 V) (W : Finset V) (F T : Finset E) :
    Prop :=
  T ⊆ F ∧ IsTreeOn ends W T

/-- `T` is a spanning tree of the whole graph `G = (V, E)`. -/
def IsSpanningTree [Fintype V] [Fintype E] [DecidableEq E] (ends : E → Sym2 V)
    (T : Finset E) : Prop :=
  IsSpanningTreeOn ends Finset.univ Finset.univ T

/-- `G` has `k` edge-disjoint spanning trees: a `k`-indexed family of pairwise disjoint edge
sets, each a spanning tree of `G`. -/
def HasKTrees [Fintype V] [Fintype E] [DecidableEq E] (k : ℕ) (ends : E → Sym2 V) : Prop :=
  ∃ T : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ ∀ i, IsSpanningTree ends (T i)

open Classical in
/-- `E_P(G)`: the edges of `G` joining vertices in different members of the partition `P`
of `V(G)` (parallel edges counted separately). -/
noncomputable def crossing [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) : Finset E :=
  Finset.univ.filter fun e => ∃ u v, ends e = s(u, v) ∧ P.part u ≠ P.part v

open Classical in
/-- `E_X`: the edges of `G` joining two elements of `X` (both ends in `X`). -/
noncomputable def edgesIn [Fintype E] (ends : E → Sym2 V) (X : Finset V) : Finset E :=
  Finset.univ.filter fun e => ∀ v ∈ ends e, v ∈ X

/-- `Δ_G(X) = k(|X| − 1) − e_X`, an integer, with `e_X = |E_X|`. -/
noncomputable def Delta [Fintype E] (k : ℕ) (ends : E → Sym2 V) (X : Finset V) : ℤ :=
  (k : ℤ) * ((X.card : ℤ) - 1) - ((edgesIn ends X).card : ℤ)

/-- The partition `P` of `V(G)` is admissible: it satisfies (1), `|E_P(G)| ≥ k(|P| − 1)`. -/
def IsAdmissiblePartition [Fintype V] [DecidableEq V] [Fintype E] (k : ℕ)
    (ends : E → Sym2 V) (P : Finpartition (Finset.univ : Finset V)) : Prop :=
  (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ)

/-- The partition `P` of `V(G)` is critical: `|E_P(G)| = k(|P| − 1)`. -/
def IsCriticalPartition [Fintype V] [DecidableEq V] [Fintype E] (k : ℕ)
    (ends : E → Sym2 V) (P : Finpartition (Finset.univ : Finset V)) : Prop :=
  ((crossing ends P).card : ℤ) = (k : ℤ) * ((P.parts.card : ℤ) - 1)

/-- `G` is admissible: every partition of `V(G)` is admissible. -/
def IsAdmissible [Fintype V] [DecidableEq V] [Fintype E] (k : ℕ) (ends : E → Sym2 V) : Prop :=
  ∀ P : Finpartition (Finset.univ : Finset V), IsAdmissiblePartition k ends P

/-- `G` is critical: `|E(G)| = k(|V(G)| − 1)`. -/
def IsCritical [Fintype V] [Fintype E] (k : ℕ) (_ends : E → Sym2 V) : Prop :=
  (Fintype.card E : ℤ) = (k : ℤ) * ((Fintype.card V : ℤ) - 1)

end NashWilliams61.TreePacking


