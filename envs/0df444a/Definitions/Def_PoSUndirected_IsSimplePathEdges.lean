-- Prove2me | Definitions.Def_PoSUndirected_IsSimplePathEdges
-- name    : PoSUndirected_IsSimplePathEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:44.72165+00:00
-- url     : https://prove2.me/theorems/9b5db71f-f713-491e-879a-5ead3ee66d22
-- title:
--   Walks, simple paths, cycles and spanning trees in a finite undirected multigraph
-- statement:
--   A finite undirected **multigraph** is given by a finite vertex set $V$, a finite edge set $E$ and, for each edge $e$, the unordered pair $\{u,v\}$ of its endpoints. Parallel edges are distinct elements of $E$.
--
--   1. A **walk** from $u$ to $v$ is a vertex sequence $u=v_0,v_1,\dots,v_m=v$ together with an edge sequence $e_1,\dots,e_m$ such that $e_j$ joins $v_{j-1}$ and $v_j$ for every $j$; vertices and edges may repeat.
--   2. An edge set $S\subseteq E$ is a **simple $u$–$v$ path** if it is the edge set $\{e_1,\dots,e_m\}$ of a walk from $u$ to $v$ whose vertices $v_0,\dots,v_m$ are pairwise distinct. For $u=v$ the only simple path is the empty one.
--   3. An edge set $C$ is a **cycle** if it is the edge set of a closed walk $v_0,v_1,\dots,v_{m-1},v_0$ ($m\ge1$) with pairwise distinct vertices and pairwise distinct edges; two distinct parallel edges form a cycle of length two.
--   4. An edge set is **acyclic** if it contains no cycle, and a **spanning tree** is an acyclic edge set that contains a simple $u$–$v$ path for every two vertices $u,v\in V$.
--
--   These are the path and forest notions of the network design model: players choose simple paths, the properness lemma speaks about acyclic unions of two paths, and the optimum of the lower construction is a minimum spanning tree.
--
--   **Formalization Note** The endpoint pair of an edge is an element of `Sym2 V`. A simple path is identified with its edge set; its edges are distinct because its vertices are, and it is determined by its endpoints and its edge set.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §2, p.2 (PDF p.4); Lemma A.1, p.13 (PDF p.15); §A.4, p.17 (PDF p.19)

import Mathlib

namespace PoSUndirected

variable {V E : Type*}

/-- Walks in a finite undirected multigraph (Tsoufis, *The Price of Stability in Undirected
Network Design: Lower Bounds and Structural Guarantees*, preprint, sha256 c095d811…, §2, p.2
(PDF p.4)). The multigraph is given by `ends : E → Sym2 V`, the unordered pair of endpoints of
each edge. `IsWalkVE ends vs es` says that the vertex list `vs = [v₀, …, v_m]` is nonempty and
the edge list `es = [e₁, …, e_m]` satisfies `ends eⱼ = {vⱼ₋₁, vⱼ}` for every `j`.

**Formalization Note.** Parallel edges are distinct elements of `E`, as in §2 ("Parallel physical
edges are distinct"). Edges are undirected, so a walk may traverse an edge in either direction. -/
def IsWalkVE (ends : E → Sym2 V) (vs : List V) (es : List E) : Prop :=
  vs ≠ [] ∧ es.map ends = (vs.zip vs.tail).map (fun p => s(p.1, p.2))

/-- `es` is the edge list of a walk from `u` to `v` (a walk may repeat vertices and edges). -/
def IsWalk (ends : E → Sym2 V) (u v : V) (es : List E) : Prop :=
  ∃ vs : List V, IsWalkVE ends vs es ∧ vs.head? = some u ∧ vs.getLast? = some v

/-- `S` is the edge set of a simple `u`–`v` path (§2, p.2 (PDF p.4): "chooses any simple
`sᵢ`–`tᵢ` path"): there are a vertex list `u = v₀, …, v_m = v` with pairwise distinct vertices and
an edge list `e₁, …, e_m` with `ends eⱼ = {vⱼ₋₁, vⱼ}` and `{e₁, …, e_m} = S`.

**Formalization Note.** A simple path is identified with its edge set. Its edges are pairwise
distinct because its vertices are, and a simple path is determined by its endpoints and its edge
set. For `u = v` the only simple path is the empty one (`S = ∅`), the "trivial pair" of §2. -/
def IsSimplePathEdges [DecidableEq E] (ends : E → Sym2 V) (u v : V) (S : Finset E) : Prop :=
  ∃ (vs : List V) (es : List E), IsWalkVE ends vs es ∧ vs.Nodup ∧ vs.head? = some u ∧
    vs.getLast? = some v ∧ es.toFinset = S

/-- `C` is the edge set of a cycle: a nonempty list of pairwise distinct vertices
`v₀, …, v_{m-1}` and pairwise distinct edges `e₁, …, e_m` with `ends eⱼ = {vⱼ₋₁, vⱼ mod m}`, and
`{e₁, …, e_m} = C`. Two distinct parallel edges form a cycle of length two. -/
def IsCycleEdges [DecidableEq E] (ends : E → Sym2 V) (C : Finset E) : Prop :=
  ∃ (vs : List V) (es : List E), vs ≠ [] ∧ vs.Nodup ∧ es.Nodup ∧
    es.map ends = (vs.zip (vs.tail ++ vs.take 1)).map (fun p => s(p.1, p.2)) ∧ es.toFinset = C

/-- An edge set is acyclic (a forest) if it contains the edge set of no cycle (Lemma A.1,
p.13 (PDF p.15): "the union of any two player paths is acyclic"). -/
def IsAcyclicEdges [DecidableEq E] (ends : E → Sym2 V) (S : Finset E) : Prop :=
  ∀ C ⊆ S, ¬ IsCycleEdges ends C

/-- A spanning tree of the multigraph (§A.4, p.17 (PDF p.19)): an acyclic edge set that joins
every two vertices of `V` by a simple path inside it. -/
def IsSpanningTree [DecidableEq E] (ends : E → Sym2 V) (T : Finset E) : Prop :=
  IsAcyclicEdges ends T ∧ ∀ u v : V, ∃ S ⊆ T, IsSimplePathEdges ends u v S

end PoSUndirected


