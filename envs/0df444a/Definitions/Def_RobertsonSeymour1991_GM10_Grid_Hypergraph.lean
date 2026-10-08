-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Grid_Hypergraph
-- name    : RobertsonSeymour1991_GM10_Grid_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:12:53.819889+00:00
-- url     : https://prove2.me/theorems/e022e293-0952-4a92-89d0-156121e7ab05
-- title:
--   §1 — hypergraphs, subhypergraphs, separations and order
-- statement:
--   A **hypergraph** $G$ has a vertex set $V(G)$, an edge set $E(G)$, and a relation saying which vertices are incident with each edge. An edge may have any number of ends, including zero. Its size is the number of its ends, and $\gamma(G)$ is the maximum edge size, taken as zero when there are no edges.
--
--   A **subhypergraph** $A$ of $G$ consists of subsets $V(A)\subseteq V(G)$ and $E(A)\subseteq E(G)$, with every end of an edge in $E(A)$ belonging to $V(A)$. Its incidence relation is inherited from $G$. Union and intersection act on both sets. A **separation** $(A,B)$ satisfies
--
--   $$A\cup B=G,\qquad E(A\cap B)=\varnothing,$$
--
--   and its **order** is $|V(A\cap B)|$. These are the objects used to orient the low-order separations of the grid.
--
--   **Formalization Note** Vertex and edge sets are types; all uses in this paper are finite. Subhypergraphs are represented by sets of each type. The definitions also include the shared edge-size convention for later missions of this paper. The maximum of an empty edge set is zero.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 153–154, §1; p. 156, edge size; p. 165, γ(G)

import Mathlib

namespace RobertsonSeymour1991.GM10.Grid

/-- §1, p. 154: a (finite) hypergraph with vertex set `V`, edge set `E` and an incidence relation. -/
structure Hypergraph (V E : Type) where
  /-- `inc e v`: the edge `e` is incident with the vertex `v`. -/
  inc : E → V → Prop

variable {V E : Type}

namespace Hypergraph

/-- p. 156: the ends of `e`, the vertices incident with `e`. -/
def ends (G : Hypergraph V E) (e : E) : Set V := {v | G.inc e v}

/-- p. 156: the size of `e`, the number of its ends. -/
noncomputable def size (G : Hypergraph V E) (e : E) : ℕ := (G.ends e).ncard

/-- p. 165: `γ(G)`, the maximum size of an edge (`0` if `E(G) = ∅`). -/
noncomputable def maxEdgeSize (G : Hypergraph V E) : ℕ := sSup (Set.range G.size)

/-- p. 154: a subhypergraph `G'` of `G`, given by `V(G') ⊆ V(G)`, `E(G') ⊆ E(G)`; incidence is inherited,
so condition (ii) says that every end of an edge of `G'` is a vertex of `G'`. -/
@[ext] structure Sub (G : Hypergraph V E) where
  verts : Set V
  edges : Set E
  ends_subset : ∀ e ∈ edges, G.ends e ⊆ verts

namespace Sub

variable {G : Hypergraph V E}

/-- `G` itself, as a subhypergraph of `G`. -/
def top (G : Hypergraph V E) : G.Sub := ⟨Set.univ, Set.univ, fun _ _ _ _ => trivial⟩

/-- p. 154: `G₁ ∪ G₂ = (V₁ ∪ V₂, E₁ ∪ E₂)`. -/
def union (A B : G.Sub) : G.Sub :=
  ⟨A.verts ∪ B.verts, A.edges ∪ B.edges, fun e he _ hv =>
    he.elim (fun h => Or.inl (A.ends_subset e h hv)) (fun h => Or.inr (B.ends_subset e h hv))⟩

/-- p. 154: `G₁ ∩ G₂ = (V₁ ∩ V₂, E₁ ∩ E₂)`. -/
def inter (A B : G.Sub) : G.Sub :=
  ⟨A.verts ∩ B.verts, A.edges ∩ B.edges, fun e he _ hv =>
    ⟨A.ends_subset e he.1 hv, B.ends_subset e he.2 hv⟩⟩

/-- `A ⊆ B` as subhypergraphs. -/
def le (A B : G.Sub) : Prop := A.verts ⊆ B.verts ∧ A.edges ⊆ B.edges

end Sub

/-- p. 153: `(A, B)` is a separation of `G`: `A ∪ B = G` and `E(A ∩ B) = ∅`. -/
def IsSeparation {G : Hypergraph V E} (A B : G.Sub) : Prop :=
  A.union B = Sub.top G ∧ A.edges ∩ B.edges = ∅

/-- p. 153: the order `|V(A ∩ B)|` of `(A, B)`. -/
noncomputable def order {G : Hypergraph V E} (A B : G.Sub) : ℕ := (A.verts ∩ B.verts).ncard

end Hypergraph

end RobertsonSeymour1991.GM10.Grid


