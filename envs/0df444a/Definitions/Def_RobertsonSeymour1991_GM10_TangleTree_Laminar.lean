-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Laminar
-- name    : RobertsonSeymour1991_GM10_TangleTree_Laminar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:19.955729+00:00
-- url     : https://prove2.me/theorems/64c668de-c508-4bda-8b20-7f8d18d45ed8
-- title:
--   §9, p. 177 — crossing separations, laminar sets, separations made by an edge of a tree-decomposition
-- statement:
--   Let $(A_1,B_1)$, $(A_2,B_2)$ be separations of a hypergraph $G$. They **cross** unless either
--   $$A_1\subseteq A_2,\ B_2\subseteq B_1,\quad\text{or}\quad A_1\subseteq B_2,\ A_2\subseteq B_1,\quad\text{or}\quad B_1\subseteq A_2,\ B_2\subseteq A_1,\quad\text{or}\quad B_1\subseteq B_2,\ A_2\subseteq A_1.$$
--   A set of separations is **laminar** if no two of its members cross.
--
--   Let $(T,\tau)$ be a tree-decomposition of $G$ and $e=uw$ an edge of $T$. Let $T_1$, $T_2$ be the components of $T\setminus e$ containing $u$ and $w$ respectively, and
--   $$G^e_i=\bigcup(\tau(t): t\in V(T_i))\qquad(i=1,2).$$
--   Then $(G^e_1,G^e_2)$ is a separation of $G$; $(G^e_1,G^e_2)$ and $(G^e_2,G^e_1)$ are the two **separations made by $e$**.
--
--   Laminar sets of separations are exactly the sets that can be realised by the edges of a tree-decomposition, which is how tangles are organised into a tree in §10.
--
--   **Formalization Note** `side D u w` is the vertex set of the component of $T\setminus uw$ containing $u$, `subUnion D S` is $\bigcup(\tau(t):t\in S)$, and `madeBy D u w` is $(G^e_1,G^e_2)$ with $u$'s side first, so the two separations made by $uw$ are `madeBy D u w` and `madeBy D w u`. `Makes D e p` says that the unordered tree edge `e` makes $p$ in one of its two orientations. These are only applied to adjacent $u,w$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 177, §9 (cross, laminar, separations made by an edge)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TangleTree

variable {V E : Type}

namespace Hypergraph

/-- p. 177: the separations `(A₁, B₁)`, `(A₂, B₂)` cross unless `A₁ ⊆ A₂` and `B₂ ⊆ B₁`, or
`A₁ ⊆ B₂` and `A₂ ⊆ B₁`, or `B₁ ⊆ A₂` and `B₂ ⊆ A₁`, or `B₁ ⊆ B₂` and `A₂ ⊆ A₁`. -/
def Crosses {G : Hypergraph V E} (p q : G.Sub × G.Sub) : Prop :=
  ¬ ((p.1.le q.1 ∧ q.2.le p.2) ∨ (p.1.le q.2 ∧ q.1.le p.2) ∨
     (p.2.le q.1 ∧ q.2.le p.1) ∨ (p.2.le q.2 ∧ q.1.le p.1))

/-- p. 177: a set of separations is laminar if no two of its members cross. -/
def IsLaminar {G : Hypergraph V E} (S : Set (G.Sub × G.Sub)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ¬ Crosses p q

end Hypergraph

namespace TreeDecomposition

variable {G : Hypergraph V E} {n : ℕ}

/-- p. 177: `⋃ (τ(t) : t ∈ S)`, the union of the pieces at a set `S` of nodes of the tree. -/
def subUnion (D : TreeDecomposition G n) (S : Set (Fin n)) : G.Sub :=
  ⟨⋃ t ∈ S, (D.τ t).verts, ⋃ t ∈ S, (D.τ t).edges, fun e he v hv => by
    simp only [Set.mem_iUnion] at he ⊢
    obtain ⟨t, ht, het⟩ := he
    exact ⟨t, ht, (D.τ t).ends_subset e het hv⟩⟩

/-- p. 177: for an edge `uw` of `T`, the vertex set of the component of `T \ uw` containing `u`. -/
def side (D : TreeDecomposition G n) (u w : Fin n) : Set (Fin n) :=
  {t | (D.T.deleteEdges {s(u, w)}).Reachable u t}

/-- p. 177: `(G₁ᵉ, G₂ᵉ)` for the edge `e = uw` of `T`, where `T₁` is the component of `T \ e`
containing `u` and `T₂` the one containing `w`. The two separations made by `e` are
`D.madeBy u w` and `D.madeBy w u`. -/
def madeBy (D : TreeDecomposition G n) (u w : Fin n) : G.Sub × G.Sub :=
  (D.subUnion (D.side u w), D.subUnion (D.side w u))

/-- p. 177: the separation `p` is made by the edge `e` of `T` (in one of its two orientations). -/
def Makes (D : TreeDecomposition G n) (e : Sym2 (Fin n)) (p : G.Sub × G.Sub) : Prop :=
  ∃ u w, e = s(u, w) ∧ D.T.Adj u w ∧ D.madeBy u w = p

end TreeDecomposition

end RobertsonSeymour1991.GM10.TangleTree


