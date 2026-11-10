-- Prove2me | Definitions.Def_MinColorPath_MinorFree_Diagram
-- name    : MinColorPath_MinorFree_Diagram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:11:08.013732+00:00
-- url     : https://prove2.me/theorems/fce7fd14-2cfd-4ad4-8b54-a8d3d4d51d72
-- title:
--   The d-diagram of a subgraph G′ in a colored graph
-- statement:
--   Let $\mathcal G=(G,P,\mathrm{cl})$ be a colored graph, $G'$ a subgraph of $G$ and $d\ge0$. Put $P'=\mathrm{cl}(V(G'))$. The **$d$-diagram** of $G'$ in $\mathcal G$ is the colored graph $\mathcal D=(D,P',\mathrm{cl}')$ where $D$ is the disjoint union of $G'$ (the **base part**) and $\Gamma^d_{\mathcal G}[P']$ (the **color part**), together with an edge $v\tau$ for every $v\in V(G')$ and $\tau\in\mathrm{cl}(v)$, and
--   $$\mathrm{cl}'(v)=\mathrm{cl}(v)\ (v\in V(G')),\qquad \mathrm{cl}'(\tau)=\{\tau\}\ (\tau\in P').$$
--   The distances in the color part are those of the whole $\Gamma_{\mathcal G}$. The diagram of $G'$ is its $1$-diagram; the diagram of a path $\pi$ is the diagram of the subgraph formed by the vertices and edges of $\pi$.
--
--   **Formalization Note.** `G'` is a Mathlib `G.Subgraph` (a path enters as `π.toSubgraph`). The vertex type is the sum `↥(subVerts H) ⊕ ↥(diagPal cl H)`; `diagGraph cl d H` is $D$ and `diagCl cl H` is $\mathrm{cl}'$. `baseIn B v` says that the base copy of the vertex $v$ lies in the set $B\subseteq V(D)$.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), pp. 17–18, the d-diagram and Fact 3.1

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_ColoredGraph

set_option autoImplicit false

/-!
# The d-diagram of a subgraph (pp. 17–18)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), pp. 17–18, the `d`-diagram and Fact 3.1.

For a colored graph `(G, P, cl)`, a subgraph `G'` of `G` and `d ≥ 0`: `P' = cl(V(G'))`; the graph
`D` is the disjoint union of `G'` and `Γ^d_G[P']` plus the edges `vτ` for `v ∈ V(G')`, `τ ∈ cl(v)`;
`cl'(v) = cl(v)` on base vertices and `cl'(τ) = {τ}` on color vertices.

Conventions.
* The subgraph `G'` is a Mathlib `G.Subgraph`; a path `π` enters as `π.toSubgraph` (its vertices
  and its edges, not the induced subgraph on its vertices).
* The vertex type of `D` is the sum `↥V(G') ⊕ ↥P'` of the base part and the color part.
* Adjacency in the color part uses distances in the whole `Γ_G`, not in `Γ_G[P']` (p. 17).
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

variable {V C : Type} [Fintype V]

/-- `V(G')` as a finite set. -/
def subVerts {G : SimpleGraph V} (H : G.Subgraph) : Finset V :=
  Finset.univ.filter fun v => v ∈ H.verts

/-- `P' = cl(V(G'))`, the palette of the diagram. -/
def diagPal {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph) : Finset C :=
  colSet cl (subVerts H)

/-- The vertex type `V(G') ⊕ P'` of the diagram: base part on the left, color part on the right. -/
abbrev DV {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph) : Type :=
  ↥(subVerts H) ⊕ ↥(diagPal cl H)

/-- The adjacency of the `d`-diagram `D` of `G'` in `G` (p. 17). -/
def diagAdj {G : SimpleGraph V} (cl : V → Finset C) (d : ℕ) (H : G.Subgraph) :
    DV cl H → DV cl H → Prop
  | Sum.inl u, Sum.inl v => H.Adj u.1 v.1
  | Sum.inl u, Sum.inr τ => τ.1 ∈ cl u.1
  | Sum.inr τ, Sum.inl u => τ.1 ∈ cl u.1
  | Sum.inr τ, Sum.inr τ' => (colorPowGraph cl d).Adj τ.1 τ'.1

lemma diagAdj_symm {G : SimpleGraph V} (cl : V → Finset C) (d : ℕ) (H : G.Subgraph)
    (x y : DV cl H) : diagAdj cl d H x y → diagAdj cl d H y x := by
  cases x <;> cases y <;> simp only [diagAdj] <;> intro h
  · exact H.adj_symm h
  · exact h
  · exact h
  · exact (colorPowGraph cl d).adj_symm h

lemma diagAdj_irrefl {G : SimpleGraph V} (cl : V → Finset C) (d : ℕ) (H : G.Subgraph)
    (x : DV cl H) : ¬ diagAdj cl d H x x := by
  cases x <;> simp only [diagAdj]
  · exact fun h => G.loopless.irrefl _ (H.adj_sub h)
  · exact (colorPowGraph cl d).loopless.irrefl _

/-- The base graph `D` of the `d`-diagram of `G'` in `G` (p. 17). -/
def diagGraph {G : SimpleGraph V} (cl : V → Finset C) (d : ℕ) (H : G.Subgraph) :
    SimpleGraph (DV cl H) where
  Adj := diagAdj cl d H
  symm := ⟨diagAdj_symm cl d H⟩
  loopless := ⟨diagAdj_irrefl cl d H⟩

/-- The coloring `cl'` of the diagram (p. 18): `cl'(v) = cl(v)`, `cl'(τ) = {τ}`. -/
def diagCl {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph) : DV cl H → Finset C
  | Sum.inl v => cl v.1
  | Sum.inr τ => {τ.1}

/-- A vertex `v` of `G` lies in the base part of a set `B ⊆ V(D)`. -/
def baseIn {G : SimpleGraph V} {cl : V → Finset C} {H : G.Subgraph} (B : Finset (DV cl H))
    (v : V) : Prop :=
  ∃ h : v ∈ subVerts H, (Sum.inl ⟨v, h⟩ : DV cl H) ∈ B

/-- A color `τ` lies in the color part of a set `B ⊆ V(D)`. -/
def colorIn {G : SimpleGraph V} {cl : V → Finset C} {H : G.Subgraph} (B : Finset (DV cl H))
    (τ : C) : Prop :=
  ∃ h : τ ∈ diagPal cl H, (Sum.inr ⟨τ, h⟩ : DV cl H) ∈ B

end

end MinColorPath.MinorFree


