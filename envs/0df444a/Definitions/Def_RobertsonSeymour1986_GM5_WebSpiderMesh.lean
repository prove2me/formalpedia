-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh
-- name    : RobertsonSeymour1986_GM5_WebSpiderMesh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:55:46.125588+00:00
-- url     : https://prove2.me/theorems/56daf023-1f27-4573-8feb-39662556b221
-- title:
--   Webs, spiders and meshes
-- statement:
--   Two subgraphs of a graph are **disjoint** if they have no common vertex, and otherwise they **meet**.
--
--   1. An **$(m,n)$-web** in $G$ is a pair $((A_1,\dots,A_m),(B_1,\dots,B_n))$ of families of paths of $G$ such that
--      (i) $A_1,\dots,A_m$ are disjoint, and $B_1,\dots,B_n$ are disjoint;
--      (ii) each $A_i$ meets each $B_j$;
--      (iii) $A_1,\dots,A_m,B_1,\dots,B_n$ are pairwise edge-disjoint.
--      ($m=0$ and $n=0$ are permitted.)
--   2. A **spider** of such a web is a connected subgraph $C$ of $G$ that is edge-disjoint from $B_1,\dots,B_n$ and, for each $i$, has a unique vertex in common with $A_i$, that vertex having valency $1$ in $C$.
--   3. An **$(m,n)$-mesh** in $G$ is a pair $((A_1,\dots,A_m),(B_1,\dots,B_n))$ of families of connected subgraphs of $G$ such that the $A_i$ are disjoint, the $B_j$ are disjoint, and each $A_i$ meets each $B_j$.
--
--   Meshes relax webs: their members are arbitrary connected subgraphs and an $A_i$ may share edges with a $B_j$. Large webs and meshes play the role of grids: the paper shows that graphs without a $\theta$-grid minor contain no $(\theta_2,\theta_2)$-web and no $(\theta_5,\theta_6)$-mesh.
--
--   **Formalization Note** The families are indexed by arbitrary index types (in the theorems, $\{1,\dots,m\}$ or a subset $I$ of it, which gives the paper's sub-families $(A_i : i\in I)$). The valency of $v$ in $C$ is its number of neighbours in $C$. The spider predicate does not itself require the pair to be a web; theorems state that separately.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 4, p. 97 (webs) and p. 98 (spiders), Sect. 5, p. 100 (meshes) (PDF pp. 6, 7, 9); terminology Sect. 1, p. 94; DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPathSubgraph

/-!
# Webs, spiders and meshes

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 4, pp. 97–98 (PDF pp. 6–7) and Sect. 5, p. 100 (PDF p. 9), unnumbered definitions.

Terminology (Sect. 1, p. 94, PDF p. 3): two subgraphs are *disjoint* if they have no common
vertices, and otherwise they *meet*. Here "disjoint" is `Disjoint A.verts B.verts`, "meets" is
`(A.verts ∩ B.verts).Nonempty`, and "edge-disjoint" is `Disjoint A.edgeSet B.edgeSet`.

**Formalization Note** The families `(A₁, …, A_m)`, `(B₁, …, B_n)` are indexed by arbitrary index
types `ι`, `κ` (in the theorems: `Fin m`, `Fin n`, or a subset `I` of the indices, which gives the
paper's sub-families `(A_i : i ∈ I)`).
-/

namespace RobertsonSeymour1986.GM5

variable {V : Type} {G : SimpleGraph V}

/-- An `(m, n)`-web (Sect. 4, p. 97, PDF p. 6): "An *(m, n)-web* in G is a pair ((A₁,…, A_m),
(B₁,…, B_n)), where A₁,…, A_m, B₁,…, B_n are paths of G, such that (i) A₁,…, A_m are disjoint, and
B₁,…, B_n are disjoint; (ii) each A_i meets each B_j; (iii) A₁,…, A_m, B₁,…, B_n are pairwise
edge-disjoint. (We permit m = 0 and n = 0.)"

Condition (iii) is stated for the three kinds of pairs: `A_i, A_{i'}` (`i ≠ i'`), `B_j, B_{j'}`
(`j ≠ j'`) and `A_i, B_j`. -/
def IsWeb {ι κ : Type} (A : ι → G.Subgraph) (B : κ → G.Subgraph) : Prop :=
  (∀ i, IsPathSubgraph (A i)) ∧ (∀ j, IsPathSubgraph (B j)) ∧
  Pairwise (fun i i' => Disjoint (A i).verts (A i').verts) ∧
  Pairwise (fun j j' => Disjoint (B j).verts (B j').verts) ∧
  (∀ i j, ((A i).verts ∩ (B j).verts).Nonempty) ∧
  Pairwise (fun i i' => Disjoint (A i).edgeSet (A i').edgeSet) ∧
  Pairwise (fun j j' => Disjoint (B j).edgeSet (B j').edgeSet) ∧
  (∀ i j, Disjoint (A i).edgeSet (B j).edgeSet)

/-- A spider of the web `(A, B)` (Sect. 4, p. 98, PDF p. 7): "A *spider* of this web is a connected
subgraph C of G such that (i) C is edge-disjoint from B₁,…, B_n; (ii) for 1 ≤ i ≤ m, C has a unique
vertex in common with A_i, and that vertex has valency 1 in C."

**Formalization Note** The valency of `v` in `C` is the number of neighbours of `v` in `C`,
`(C.neighborSet v).ncard`. The predicate does not itself require `(A, B)` to be a web; the theorems
state `IsWeb A B` separately. -/
def IsSpider {ι κ : Type} (A : ι → G.Subgraph) (B : κ → G.Subgraph) (C : G.Subgraph) : Prop :=
  C.Connected ∧
  (∀ j, Disjoint C.edgeSet (B j).edgeSet) ∧
  ∀ i, ∃ v : V, C.verts ∩ (A i).verts = {v} ∧ (C.neighborSet v).ncard = 1

/-- An `(m, n)`-mesh (Sect. 5, p. 100, PDF p. 9): "An *(m, n)-mesh* in a graph G is a pair
((A₁,…, A_m), (B₁,…, B_n)), where (i) A₁,…, A_m, B₁,…, B_n are all connected subgraphs of G;
(ii) A₁,…, A_m are disjoint, and B₁,…, B_n are disjoint; (iii) each A_i meets each B_j." -/
def IsMesh {ι κ : Type} (A : ι → G.Subgraph) (B : κ → G.Subgraph) : Prop :=
  (∀ i, (A i).Connected) ∧ (∀ j, (B j).Connected) ∧
  Pairwise (fun i i' => Disjoint (A i).verts (A i').verts) ∧
  Pairwise (fun j j' => Disjoint (B j).verts (B j').verts) ∧
  (∀ i j, ((A i).verts ∩ (B j).verts).Nonempty)

end RobertsonSeymour1986.GM5


