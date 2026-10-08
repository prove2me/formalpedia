-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsBasic
-- name    : StrongPerfectGraph_Main_IsBasic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:05:47.882413+00:00
-- url     : https://prove2.me/theorems/441a6361-48e2-467e-83e6-5bbd3f28dbc8
-- title:
--   Basic graph and double split graph
-- statement:
--   A graph $G$ is **basic** if $G$ or $\overline G$ is bipartite, $G$ or $\overline G$ is the line graph of a bipartite graph, or $G$ is a double split graph:
--
--   $$G\in\mathcal B_{\rm bip}\cup\overline{\mathcal B_{\rm bip}}\cup\mathcal L(\mathcal B_{\rm bip})\cup\overline{\mathcal L(\mathcal B_{\rm bip})}\cup\mathcal D.$$
--
--   A double split graph has pairs $(a_i,b_i)$ for $1\le i\le m$ and $(c_j,d_j)$ for $1\le j\le n$, with $m,n\ge2$. Each $a_i b_i$ is an edge and each $c_j d_j$ is a nonedge. Distinct $a,b$ pairs have no edges between them; distinct $c,d$ pairs have all four. Between each $a,b$ pair and $c,d$ pair, the two edges form one of the two perfect matchings. A line graph has one vertex per edge of its parent graph, adjacent exactly when the edges share an endpoint. These are the basic classes in the decomposition theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 52–53, §1, definitions of double split, line graph, and basic

import Mathlib

namespace StrongPerfectGraph.Main

/-- The four-part double split graph of p. 52. The equivalence makes the parts disjoint
and exhaustive; the cross edges form one of the two perfect matchings on each pair of pairs. -/
def IsDoubleSplit {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ m n : ℕ, 2 ≤ m ∧ 2 ≤ n ∧
    ∃ e : ((Fin m × Bool) ⊕ (Fin n × Bool)) ≃ V,
      (∀ i : Fin m, G.Adj (e (Sum.inl (i, false))) (e (Sum.inl (i, true)))) ∧
      (∀ j : Fin n, ¬ G.Adj (e (Sum.inr (j, false))) (e (Sum.inr (j, true)))) ∧
      (∀ i k : Fin m, i ≠ k → ∀ s t : Bool,
        ¬ G.Adj (e (Sum.inl (i, s))) (e (Sum.inl (k, t)))) ∧
      (∀ j k : Fin n, j ≠ k → ∀ s t : Bool,
        G.Adj (e (Sum.inr (j, s))) (e (Sum.inr (k, t)))) ∧
      (∀ i : Fin m, ∀ j : Fin n,
        (G.Adj (e (Sum.inl (i, false))) (e (Sum.inr (j, false))) ∧
         G.Adj (e (Sum.inl (i, true))) (e (Sum.inr (j, true))) ∧
         ¬ G.Adj (e (Sum.inl (i, false))) (e (Sum.inr (j, true))) ∧
         ¬ G.Adj (e (Sum.inl (i, true))) (e (Sum.inr (j, false)))) ∨
        (G.Adj (e (Sum.inl (i, false))) (e (Sum.inr (j, true))) ∧
         G.Adj (e (Sum.inl (i, true))) (e (Sum.inr (j, false))) ∧
         ¬ G.Adj (e (Sum.inl (i, false))) (e (Sum.inr (j, false))) ∧
         ¬ G.Adj (e (Sum.inl (i, true))) (e (Sum.inr (j, true)))))

/-- Isomorphism to the line graph of some finite simple graph. -/
def IsLineGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ H : SimpleGraph (Fin n), Nonempty (G ≃g H.lineGraph)

/-- The four basic classes, including the complement classes. -/
def IsBasic {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∨ Gᶜ.IsBipartite ∨
    (∃ n : ℕ, ∃ H : SimpleGraph (Fin n), H.IsBipartite ∧ Nonempty (G ≃g H.lineGraph)) ∨
    (∃ n : ℕ, ∃ H : SimpleGraph (Fin n), H.IsBipartite ∧ Nonempty (Gᶜ ≃g H.lineGraph)) ∨
    IsDoubleSplit G

end StrongPerfectGraph.Main


