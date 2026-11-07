-- Prove2me | Definitions.Def_MinBisectFPT_cutSize
-- name    : MinBisectFPT_cutSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:39.682201+00:00
-- url     : https://prove2.me/theorems/e1922f5c-da70-4a80-9256-d08563beef5f
-- title:
--   Cut $\delta_H(X)$, neighbourhood $N_H(X)$, the graphs $G[A]-E(G[S])$, components
-- statement:
--   For a graph $H$ and a vertex set $X$, the **cut** $\delta_H(X)$ is the set of edges of $H$ with exactly one endpoint in $X$, and $|\delta_H(X)|$ is the cut size of $X$. The **neighbourhood** $N_H(X)$ is the set of vertices outside $X$ with a neighbour in $X$.
--
--   The graph $G[A]-E(G[S])$ keeps the edges of $G$ with both endpoints in $A$ and not both endpoints in $S$. The subtree graph $G_t$, the bag graph $B_t$ and the graph $H_D$ of a recursive call all have this shape. A **component** of $H[W]$ is a maximal subset of $W$ inducing a connected graph; it is nonempty.
--
--   **Formalization Note** $G[A]-E(G[S])$ lives on the ambient vertex type, with the vertices outside $A$ isolated. Each "$X\subseteq V(H)$" of the paper is then written $X\subseteq A$.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §1.1, p.2; §3, p.9

import Mathlib

open scoped Classical

namespace MinBisectFPT

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The cut `δ_H(X)`.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*,
STOC 2027 submission (manuscript sha256 8db80a52…), §3, p.9: "δ_H(X) is the set of edges of H with
exactly one endpoint in X". -/
noncomputable def cutEdges (H : SimpleGraph V) (X : Finset V) : Finset (Sym2 V) :=
  Finset.univ.filter fun e => e ∈ H.edgeSet ∧ ∃ u ∈ X, ∃ v, v ∉ X ∧ e = s(u, v)

/-- The cut size `|δ_H(X)|` (ibid., §3, p.9). -/
noncomputable def cutSize (H : SimpleGraph V) (X : Finset V) : ℕ := (cutEdges H X).card

/-- `N_H(X)`, "the set of vertices outside X with a neighbor in X" (ibid., §3, p.9). -/
noncomputable def nbr (H : SimpleGraph V) (X : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ X ∧ ∃ u ∈ X, H.Adj u v

/-- The number of edges `|E(H)|`. -/
noncomputable def edgeCount (H : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun e : Sym2 V => e ∈ H.edgeSet).card

/-- `G[A] − E(G[S])`, the shape shared by the subtree graph `G_t` (§1.1, p.2), the bag graph `B_t`
(§3, p.9) and the graph `H_D` of a call of Decompose (§5, p.16).

**Formalization Note** The result lives on the ambient vertex type, with edges only inside `A`;
the vertices outside `A` are isolated. Every "X ⊆ V(H)" of the paper is then stated as `X ⊆ A`. -/
def restrictMinus (G : SimpleGraph V) (A S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ A ∧ v ∈ A ∧ ¬(u ∈ S ∧ v ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, fun h' => h.2.2.2 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- `C` is the vertex set of a component of `H[W]`: a maximal subset of `W` inducing a connected
graph. Mathlib's `Connected` includes nonemptiness, so `C` is nonempty. -/
def IsComponent (H : SimpleGraph V) (W C : Finset V) : Prop :=
  C ⊆ W ∧ (H.induce (C : Set V)).Connected ∧
    ∀ C' : Finset V, C ⊆ C' → C' ⊆ W → (H.induce (C' : Set V)).Connected → C' = C

end MinBisectFPT


