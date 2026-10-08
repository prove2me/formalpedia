-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
-- name    : RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:36:14.13715+00:00
-- url     : https://prove2.me/theorems/85622cf8-7c74-43bd-8e31-b5726a72dee9
-- title:
--   §1, pp. 153–156, 165 — hypergraph, subhypergraph, separation and its order, edge size, γ(G)
-- statement:
--   A **hypergraph** $G$ consists of a finite set $V(G)$ of vertices, a finite set $E(G)$ of edges, and an incidence relation between them; each edge may or may not be incident with each vertex. The **ends** of an edge $e$ are the vertices incident with it, and its **size** is the number of its ends. An edge may have any number of ends, including none, so graphs (with loops and parallel edges) are the special case in which every edge has one or two ends. The maximum size of an edge is
--   $$\gamma(G) = \max_{e \in E(G)} |\{v : v \text{ is an end of } e\}|,$$
--   with $\gamma(G) = 0$ when $E(G) = \emptyset$.
--
--   A **subhypergraph** $G'$ of $G$ is given by sets $V(G') \subseteq V(G)$ and $E(G') \subseteq E(G)$ such that every end of an edge of $G'$ is a vertex of $G'$; incidence is inherited from $G$. For subhypergraphs $G_1, G_2$ we write $G_1 \cup G_2$ and $G_1 \cap G_2$ for the subhypergraphs with vertex and edge sets the unions (intersections) of those of $G_1$ and $G_2$, and $G_1 \subseteq G_2$ when both sets of $G_1$ are contained in those of $G_2$. A **separation** of $G$ is a pair $(A, B)$ of subhypergraphs with $A \cup B = G$ and $E(A \cap B) = \emptyset$; its **order** is $|V(A \cap B)|$.
--
--   These are the basic objects of Robertson and Seymour's Graph Minors X, used by every statement of this mission.
--
--   **Formalization Note** $V(G)$ and $E(G)$ are the types `V` and `E`; finiteness is imposed by `[Finite V] [Finite E]` on each theorem. A subhypergraph is the structure `Sub G` of its vertex and edge sets together with the closure condition. $\gamma(G)$ is `maxEdgeSize`, the `sSup` in $\mathbb N$ of the (finite) set of edge sizes, which is $0$ for an empty edge set as the paper stipulates.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 153–154 (§1, hypergraph, subhypergraph, separation), p. 156 (ends, size), p. 165 (γ(G))

import Mathlib

namespace RobertsonSeymour1991.GM10.TreeWidth

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

end RobertsonSeymour1991.GM10.TreeWidth


