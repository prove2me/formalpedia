-- Prove2me | Definitions.Def_GenTuranHard_FinGraph
-- name    : GenTuranHard_FinGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:36.089321+00:00
-- url     : https://prove2.me/theorems/90f8b211-77f9-4b9a-b90a-c2e6c16d8996
-- title:
--   Finite graphs on $\{0,\dots,n-1\}$, $\mathcal F$-freeness, $\hom(Q,G)$, $e(G)$, $p(Q)$, $K_k$ and $K_2\cup qK_1$
-- statement:
--   The graphs of the paper are finite and simple (§2, p.4). A **finite graph** is encoded as a pair $G = (n, \mathrm{Adj})$ with vertex set $\{0, \dots, n-1\}$; $v(G) = n$. Every finite graph is isomorphic to one of this form. A graph $T$ on an arbitrary finite vertex set is renumbered on $\{0,\dots,v(T)-1\}$ by a fixed bijection when needed.
--
--   For a family $\mathcal F$ of such graphs (finite or infinite), a graph $H$ is **$\mathcal F$-free** if no member of $\mathcal F$ is a (not necessarily induced) subgraph of $H$, i.e. no $F \in \mathcal F$ has an injective homomorphism into $H$ (p.2).
--
--   The module also fixes the basic counts:
--
--   1. $\hom(Q, G)$, the number of homomorphisms (adjacency-preserving, not necessarily injective maps $V(Q) \to V(G)$) from $Q$ to $G$ (p.4);
--   2. $e(G)$, the number of edges;
--   3. $p(Q)$, the number of nonisolated vertices of $Q$ (p.14);
--   4. the complete graph $K_k$ on $\{0,\dots,k-1\}$, and $K_2 \cup qK_1$ on $\{0,\dots,q+1\}$ with the single edge $01$ (p.15).
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** $\hom(Q,G)$ is the cardinality of the finite set of graph homomorphisms. All quantities are invariant under renumbering the vertices, so the choice of the bijection in the renumbering is immaterial.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §2, pp.2 and 4 (F-free, hom); p.14 (p(Q)); Lemma 4.5, p.15 (K₂ ∪ qK₁)

import Mathlib

set_option autoImplicit false

namespace GenTuranHard

/-- A **finite simple graph** with vertex set `{0, …, n − 1}` (Chen, He, Li, Ma, Xie, *NP-hardness of
additive approximation for generalized Turán problems*, arXiv:2610.16358, sha256 dc85633a…, §2, p.4:
"In this paper, all graphs are finite and simple"). `G.1 = v(G)` is the number of vertices and `G.2`
the adjacency relation on `Fin G.1`. Host graphs, members of forbidden families and the quotient graphs
of §4.1 are all of this form.

**Formalization Note** Every finite simple graph is isomorphic to one of this form; all quantities of
the mission (copy counts, homomorphism counts, freeness, chromatic number) are isomorphism-invariant. -/
abbrev FinGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The finite graph `T` renumbered on `Fin v(T)` through `Fintype.equivFin` (an arbitrary but fixed
numbering; every quantity of the mission is invariant under the choice). -/
noncomputable def toFin {W : Type} [Fintype W] (T : SimpleGraph W) : FinGraph :=
  ⟨Fintype.card W, T.comap (Fintype.equivFin W).symm⟩

/-- `H` is **𝓕-free** (p.2): it contains no member of the family `Fam` as a (not necessarily induced)
subgraph, i.e. no `F ∈ Fam` has a copy (injective homomorphism) in `H`. The family may be finite or
infinite. -/
def FamFree (Fam : Set FinGraph) {V : Type} (H : SimpleGraph V) : Prop :=
  ∀ F ∈ Fam, F.2.Free H

/-- `hom(Q, G)` (p.4): the number of homomorphisms (not necessarily injective adjacency-preserving maps)
from `Q` to `G`. For finite vertex types the set of homomorphisms is finite, so `Nat.card` is its
cardinality. -/
noncomputable def homCount {V W : Type} (Q : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (Q →g G)

/-- `e(G)` (p.2): the number of edges of `G`. -/
noncomputable def edgeCount {V : Type} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

open scoped Classical in
/-- `p(Q)` (p.14): the number of nonisolated vertices of `Q`, i.e. of vertices of positive degree. -/
noncomputable def pNon (Q : FinGraph) : ℕ :=
 (Finset.univ.filter (fun v : Fin Q.1 => ∃ w, Q.2.Adj v w)).card

/-- The complete graph `K_k` as a finite graph on `Fin k`. -/
def cliqueFG (k : ℕ) : FinGraph := ⟨k, ⊤⟩

/-- The graph `K₂ ∪ qK₁` on `Fin (q + 2)`: one edge between the vertices `0` and `1`, and `q` isolated
vertices `2, …, q + 1` (p.15). -/
def edgePlusIsolated (q : ℕ) : SimpleGraph (Fin (q + 2)) :=
  SimpleGraph.fromEdgeSet {s(0, 1)}

end GenTuranHard


