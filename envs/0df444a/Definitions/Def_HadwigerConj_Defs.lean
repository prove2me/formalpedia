-- Prove2me | Definitions.Def_HadwigerConj_Defs
-- name    : HadwigerConj_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T23:08:46.438249+00:00
-- url     : https://prove2.me/theorems/3214721d-af9e-4762-b23c-2344042eb26a
-- title:
--   Graph minors, complete minors, the statement $\mathrm{HC}(t)$, and degeneracy
-- statement:
--   All graphs are simple (no loops or parallel edges).
--
--   1. **Minor.** A graph $H$ with vertex set $W$ is a *minor* of a graph $G$ with vertex set $V$ if there are *branch sets* $B_w\subseteq V$, one for each $w\in W$, such that each $B_w$ induces a connected (hence nonempty) subgraph of $G$, distinct branch sets are disjoint, and for every edge $w_1w_2$ of $H$ some vertex of $B_{w_1}$ is adjacent in $G$ to some vertex of $B_{w_2}$. This is equivalent to the usual definition: $H$ is isomorphic to a graph obtained from a subgraph of $G$ by contracting edges.
--   2. **Complete minor.** $G$ has a $K_t$ *minor* if the complete graph $K_t$ is a minor of $G$.
--   3. **$\mathrm{HC}(t)$.** For an integer $t\ge 0$, $\mathrm{HC}(t)$ is the statement “every finite graph with no $K_{t+1}$ minor is $t$-colourable”.
--   4. **Degeneracy.** $G$ is *$k$-degenerate* if every nonempty set $S$ of vertices contains a vertex having at most $k$ neighbours in $S$.
--
--   These are the basic notions of Seymour's survey (Section 1 and Section 3) and are shared by every statement of this mission.
--
--   **Formalization Note** Minors are encoded by branch sets (a *minor model*). $\mathrm{HC}(t)$ quantifies over all finite vertex types in `Type`. Degeneracy is phrased with induced subgraphs (vertex subsets); this is equivalent to the survey's “every non-null subgraph has a vertex of degree at most $k$”, since passing from a subgraph to the induced subgraph on the same vertex set can only raise degrees.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 1 (definition of minor, statement 1.1 and HC(t)) and Section 3 (definition of k-degenerate, p. 4); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory)

import Mathlib

namespace HadwigerConj

/-- `IsMinor H G`: the graph `H` is a minor of the graph `G`, expressed through branch sets.
There is a family `B w` (one for each vertex `w` of `H`) of vertex sets of `G` such that
each `B w` induces a connected (in particular nonempty) subgraph of `G`, distinct branch sets
are disjoint, and whenever `w₁ w₂` is an edge of `H` some vertex of `B w₁` is adjacent in `G`
to some vertex of `B w₂`. -/
def IsMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂)) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ u ∈ B w₁, ∃ v ∈ B w₂, G.Adj u v)

/-- `HasCompleteMinor G t`: the complete graph `K_t` is a minor of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  IsMinor (⊤ : SimpleGraph (Fin t)) G

/-- `HC t`: every finite graph with no `K_{t+1}` minor is `t`-colourable. -/
def HC (t : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ HasCompleteMinor G (t + 1) → G.Colorable t

/-- `IsDegenerate G k`: every nonempty set `S` of vertices contains a vertex with at most `k`
neighbours inside `S` (i.e. every non-null induced subgraph has a vertex of degree `≤ k`). -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ k

end HadwigerConj


