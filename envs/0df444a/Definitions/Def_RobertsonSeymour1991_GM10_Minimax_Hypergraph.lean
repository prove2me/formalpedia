-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
-- name    : RobertsonSeymour1991_GM10_Minimax_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:11:41.140843+00:00
-- url     : https://prove2.me/theorems/9b3e4191-b0ba-471a-8b1d-71a9f5a51100
-- title:
--   §1–§2, pp. 153–157 — hypergraph, subhypergraph, separation and its order, edge size, γ(G), G\X and K_e
-- statement:
--   A **hypergraph** $G$ consists of a finite set $V(G)$ of vertices, a finite set $E(G)$ of edges and an incidence relation; each edge may or may not be incident with each vertex, and an edge may have any number of ends, including none.
--
--   1. The **ends** of an edge $e$ are the vertices incident with $e$; the **size** of $e$ is the number of its ends. $\gamma(G)$ is the maximum size of an edge of $G$, with $\gamma(G)=0$ if $E(G)=\emptyset$.
--   2. A **subhypergraph** $G'\subseteq G$ is given by $V(G')\subseteq V(G)$ and $E(G')\subseteq E(G)$ with the inherited incidence; it must contain every end of each of its edges. For subhypergraphs $G_1,G_2$, $G_1\cup G_2=(V_1\cup V_2,E_1\cup E_2)$ and $G_1\cap G_2=(V_1\cap V_2,E_1\cap E_2)$.
--   3. A **separation** of $G$ is a pair $(A,B)$ of subhypergraphs with $A\cup B=G$ and $E(A\cap B)=\emptyset$; its **order** is $|V(A\cap B)|$.
--   4. For $X\subseteq E(G)$, $G\setminus X$ is the subhypergraph with vertex set $V(G)$ and edge set $E(G)-X$; $G\setminus e=G\setminus\{e\}$. $K_e$ is the subhypergraph formed by the edge $e$ and its ends.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** A subhypergraph is determined by its vertex and edge sets, with a proof that the ends of its edges are among its vertices; $G$ itself is `Sub.top G`. $\gamma(G)$ is `sSup` of the edge sizes in $\mathbb N$, which is $0$ for an empty edge set and the maximum otherwise. Finiteness is a hypothesis of each theorem.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 153–154 (§1), p. 156 (size), p. 157 (K_e), p. 165 (γ(G))

import Mathlib

namespace RobertsonSeymour1991.GM10.Minimax

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

/-- p. 154: `G\X` for `X ⊆ E(G)`, the subhypergraph with `V(G\X) = V(G)` and `E(G\X) = E(G) − X`.
`G\e` is `deleteEdges {e}`. -/
def deleteEdges (G : Hypergraph V E) (X : Set E) : G.Sub := ⟨Set.univ, Xᶜ, fun _ _ _ _ => trivial⟩

/-- p. 157: `K_e`, the subhypergraph formed by the edge `e` and its ends. -/
def edgeSub (G : Hypergraph V E) (e : E) : G.Sub :=
  ⟨G.ends e, {e}, fun e' he' => by rw [Set.mem_singleton_iff.mp he']⟩

/-- p. 153: `(A, B)` is a separation of `G`: `A ∪ B = G` and `E(A ∩ B) = ∅`. -/
def IsSeparation {G : Hypergraph V E} (A B : G.Sub) : Prop :=
  A.union B = Sub.top G ∧ A.edges ∩ B.edges = ∅

/-- p. 153: the order `|V(A ∩ B)|` of `(A, B)`. -/
noncomputable def order {G : Hypergraph V E} (A B : G.Sub) : ℕ := (A.verts ∩ B.verts).ncard

end Hypergraph

end RobertsonSeymour1991.GM10.Minimax


