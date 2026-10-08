-- Prove2me | Definitions.Def_Menger27_Graphs_Parts
-- name    : Menger27_Graphs_Parts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:01.121999+00:00
-- url     : https://prove2.me/theorems/d1add08f-99ef-4526-bc75-28d252f74924
-- title:
--   pp. 101–102 — irreducibly n-point connected parts; the side K₁ of a separator S
-- statement:
--   Let $G$ be a simple graph on $V$ and $P, Q, S \subseteq V$ finite. This file defines the two objects Menger's proof of Satz δ is built from.
--
--   1. **Irreducibly $n$-point connected** (p. 101, "irreduzibel n-punktig zusammenhängend"). A graph $K$ is irreducibly $n$-point connected between $P$ and $Q$ if it is $n$-point connected between $P$ and $Q$ and no proper part of $K$ is:
--   $$K \text{ is } n\text{-point connected} \quad\text{and}\quad \forall H \subsetneq K:\ H \text{ is not } n\text{-point connected between } P \text{ and } Q .$$
--   A *part* of $K$ ("Teil") is a spanning subgraph $H$ of $K$ (same vertex set, a subset of the edges); it is proper if it lacks at least one edge of $K$.
--
--   2. **The side $K_1$ of a separating set** (p. 102). Let $C$ be the set of vertices that can be reached from a vertex of $P - S$ by a walk of $G$ that never meets $S$; these are the vertices of the components of $G - S$ that meet $P - S\cdot P$. The graph $K_1$ has the same vertices as $G$, and its edges are the edges $uv$ of $G$ with at least one end in $C$ and each end in $C$ or in $S - S\cdot P$:
--   $$E(K_1) = \{\, uv \in E(G) : \{u, v\} \cap C \neq \emptyset,\ \{u, v\} \subseteq C \cup (S - P) \,\}.$$
--   Exchanging $P$ and $Q$ gives Menger's $K_2$, with the target set $S - S\cdot Q$.
--
--   In the proof of Satz δ, an irreducible part $K'$ is cut by an $n$-point separating set $S$ into the side of $P$ and the side of $Q$; each side has smaller degree, so the induction hypothesis applies to it.
--
--   **Formalization Note.** Parts are spanning subgraphs `H ≤ K` of type `SimpleGraph V`, and "proper" is `H < K`. Since a part keeps every vertex, it always contains $P \cup Q$, which is what "zwischen P und Q" requires of a part. On p. 102 Menger's $K_1$ is a closed part of $K' - S$ containing $P - S\cdot P$ and is then treated as a space between $P - S\cdot P$ and $S - S\cdot P$. This mission takes $K_1$ to be the union of the components of $G - S$ that meet $P - S$, together with the edges from them to $S - S\cdot P$. The edges from $C$ to points of $S\cdot P$ are left out: those points belong to neither of the two sets $K_1$ is considered between, and the open arcs to them are not used by any arc from $P - S\cdot P$ to $S - S\cdot P$ inside $K_1 \subseteq K' - S$. Components of $G - S$ that meet neither $P - S$ nor $Q - S$, and edges joining two vertices of $S$, are put in neither side.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101 (irreduzibel n-punktig zusammenhängender Teil, proof of Satz δ) and p. 102 (the parts K₁, K₂ of K′ − S, proof of Satz δ)

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

/-- `IrreduciblyNPointConnected K P Q n` (Menger 1927, p. 101, "irreduzibel n-punktig
zusammenhängend"): `K` is `n`-point connected between `P` and `Q`, and no proper part of `K`
(a spanning subgraph `H < K`, i.e. `K` with at least one edge removed) is. -/
def IrreduciblyNPointConnected {V : Type*} (K : SimpleGraph V) (P Q : Finset V) (n : ℕ) :
    Prop :=
  NPointConnected K P Q n ∧ ∀ H : SimpleGraph V, H < K → ¬ NPointConnected H P Q n

/-- `sideVerts G P S` (Menger 1927, p. 102): the vertices that can be reached in `G` from a vertex
of `P − S` by a walk that never meets `S`; these are the vertices of the components of `G − S`
that meet `P − S·P`. -/
def sideVerts {V : Type*} (G : SimpleGraph V) (P S : Finset V) : Set V :=
  {v | ∃ x ∈ P, ∃ w : G.Walk x v, ∀ u ∈ w.support, u ∉ S}

/-- `sidePart G P S` (Menger 1927, p. 102, the part `K₁` together with its end points in
`S − S·P`): the spanning subgraph of `G` whose edges are the edges `uv` of `G` with at least one
end in `sideVerts G P S` and each end in `sideVerts G P S` or in `S − P`. -/
def sidePart {V : Type*} (G : SimpleGraph V) (P S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ sideVerts G P S ∨ v ∈ sideVerts G P S) ∧
    (u ∈ sideVerts G P S ∨ (u ∈ S ∧ u ∉ P)) ∧ (v ∈ sideVerts G P S ∨ (v ∈ S ∧ v ∉ P))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

end Menger27.Graphs


