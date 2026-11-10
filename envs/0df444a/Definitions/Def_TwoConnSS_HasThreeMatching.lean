-- Prove2me | Definitions.Def_TwoConnSS_HasThreeMatching
-- name    : TwoConnSS_HasThreeMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:02.965894+00:00
-- url     : https://prove2.me/theorems/15dcf2a4-4aa7-4a1f-9034-2d57e735fb43
-- title:
--   2-vertex-connectivity, non-trivial 2-vertex cuts and the 3-matching property
-- statement:
--   Let $G$ be a finite graph.
--
--   1. $G$ is **2-vertex-connected (2VC)** if it has at least three vertices and deleting any vertex leaves it connected.
--   2. A pair $\{u, v\}$ is a **non-trivial 2-vertex cut** if $V \setminus \{u, v\} = X \,\dot\cup\, Y$ with $|X|, |Y| \ge 2$ and no edge between $X$ and $Y$.
--   3. $G$ has the **3-matching property** if for every partition $V = X \,\dot\cup\, Y$ with $|X|, |Y| \ge 4$, the cut between $X$ and $Y$ contains a matching of size three: three edges $a_ib_i$ with $a_i \in X$, $b_i \in Y$, and the $a_i$ pairwise distinct and the $b_i$ pairwise distinct.
--
--   The 3-matching property is the main separator tool of the augmentation framework.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §6, p.23; Definitions 7.1–7.2, p.26

import Mathlib

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- **2-vertex-connected graph** (§6, p.23): "A graph with at least three vertices is
2-vertex-connected (2VC) if deleting any vertex leaves it connected." -/
def IsTwoVC (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected

/-- A side partition of a separator `T` (p.31): `V \ T = U ∪̇ W` with no edge of `G` between `U`
and `W`; neither side is required to be connected or nonempty. -/
def IsSidePartition (G : SimpleGraph V) (T U W : Finset V) : Prop :=
  Disjoint T U ∧ Disjoint T W ∧ Disjoint U W ∧ T ∪ U ∪ W = Finset.univ ∧
  ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w

/-- `T` is a vertex cut: it has a side partition with both sides nonempty. -/
def IsVertexCut (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ U W, IsSidePartition G T U W ∧ U.Nonempty ∧ W.Nonempty

/-- **Non-trivial 2-vertex cut** (Definition 7.1, p.26): "A pair {u, v} ⊆ V(G) is a non-trivial
2-vertex cut if there is a partition V(G) \ {u, v} = X ∪̇ Y such that |X|, |Y| ≥ 2 and
E_G(X, Y) = ∅." -/
def IsNontrivialTwoCut (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ X Y, IsSidePartition G {u, v} X Y ∧ 2 ≤ X.card ∧ 2 ≤ Y.card

/-- **The 3-matching property.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Definition 7.2, p.26: "A graph G
has the 3-matching property if, for every partition V(G) = X ∪̇ Y with |X|, |Y| ≥ 4, the cut
E_G(X, Y) contains a matching of size three."

Also defined here: 2-vertex-connectivity (p.23), side partitions and vertex cuts (p.31), and
non-trivial 2-vertex cuts (Definition 7.1).

**Formalization Note.** A matching of size three in the cut is three edges `a_i b_i` with
`a_i ∈ X`, `b_i ∉ X`, the `a_i` pairwise distinct and the `b_i` pairwise distinct. -/
def HasThreeMatching (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, 4 ≤ X.card → 4 ≤ Xᶜ.card →
    ∃ a b : Fin 3 → V, (∀ i, a i ∈ X) ∧ (∀ i, b i ∉ X) ∧ Function.Injective a ∧
      Function.Injective b ∧ ∀ i, G.Adj (a i) (b i)

end TwoConnSS


