-- Prove2me | Definitions.Def_ConstRegretMatch_Acyclic_Network
-- name    : ConstRegretMatch_Acyclic_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:00.854329+00:00
-- url     : https://prove2.me/theorems/21f26a46-b753-4afe-99e7-e96515b2b3f5
-- title:
--   §2, pp. 7–8 — the matching network: types, matches 𝒜(m), matching matrix M, λ, r and the matching network graph 𝒢
-- statement:
--   This file fixes the combinatorial data of a **matching network** and its bipartite graph.
--
--   There are $n$ agent types $\mathcal A = \{1,\dots,n\}$ and $d$ matches $\mathcal M = \{1,\dots,d\}$. Each match $m$ is a set $\mathcal A(m) \subseteq \mathcal A$ of agent types with
--   $$|\mathcal A(m)| \ge 2 \quad\text{for every } m \in \mathcal M,$$
--   and every agent type participates in at least one match. The **matching matrix** $M \in \{0,1\}^{n\times d}$ has $M_{im} = 1$ if and only if $i \in \mathcal A(m)$.
--
--   1. **Arrival probabilities** are a vector $\lambda \in \mathbb R^n$ with $\lambda_i > 0$ for every $i$ and $\sum_i \lambda_i = 1$.
--   2. **Match values** are a vector $r \in \mathbb R^d$ with $r_m > 0$ for every $m$.
--   3. For a set $S \subseteq \mathcal M$ of matches, the **incidence graph** of $S$ is the simple bipartite graph on the vertex set $\mathcal A \sqcup \mathcal M$ with an edge between type $i$ and match $m$ if and only if $m \in S$ and $i \in \mathcal A(m)$; matches outside $S$ are isolated vertices. The **matching network graph** $\mathcal G$ is the incidence graph of all matches.
--   4. A **leaf** of a graph is a vertex of degree exactly one, and $\sum_{m\in\mathcal M} M_{im}$ is the number of matches in which type $i$ participates.
--
--   These are the objects on which the static-planning problem, the general position condition and (SPP)-acyclicity are built.
--
--   **Formalization Note** Types and matches are `Fin n` and `Fin d`, 0-based (the paper's type $i$ is index $i-1$). The topology $(\mathcal A(m))_m$ with its two standing assumptions is the structure `MatchingNetwork`; $\lambda$ and $r$ are separate vectors with the predicates `IsArrivalRates` and `IsMatchValues`, because the right-hand side of the static-planning problem is varied in Theorem 5.1. The graph lives on `Fin n ⊕ Fin d`.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 7–8, §2 (Matching network and dynamics; Matching network graph); p. 44, App. C (leaves)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network

namespace ConstRegretMatch.Acyclic

/-- A matching network topology (§2, p. 7) with `n` agent types and `d` matches. Agent types are
`Fin n` and matches are `Fin d`, both 0-based: the paper's type `i ∈ {1, …, n}` is index `i - 1`, and
likewise for matches. `A m` is the set `𝒜(m)` of agent types participating in match `m`. The two
standing assumptions of §2 are fields: every match uses at least two agent types, and every agent type
participates in at least one match. -/
structure MatchingNetwork (n d : ℕ) where
  /-- `A m = 𝒜(m)`, the agent types participating in match `m`. -/
  A : Fin d → Finset (Fin n)
  /-- "Each match `m ∈ ℳ` corresponds to a subset of at least two agent types." -/
  two_le_card : ∀ m, 2 ≤ (A m).card
  /-- "We assume that each agent type is participating in at least one match." -/
  covers : ∀ i, ∃ m, i ∈ A m

variable {n d : ℕ}

/-- The matching matrix `M ∈ {0,1}^{n×d}` as a real matrix (rows: agent types, columns: matches):
`M i m = 1` iff `i ∈ 𝒜(m)`, and `0` otherwise. -/
noncomputable def MatchingNetwork.M (N : MatchingNetwork n d) : Matrix (Fin n) (Fin d) ℝ :=
  fun i m => if i ∈ N.A m then 1 else 0

/-- The bipartite incidence graph of the matches in `S` (§2, p. 8): its vertices are the agent types
(`Sum.inl i`) and the matches (`Sum.inr m`); type `i` and match `m` are adjacent iff `m ∈ S` and
`i ∈ 𝒜(m)`. There are no type–type and no match–match edges. Matches outside `S` stay as isolated
vertices. -/
def incidenceGraph (N : MatchingNetwork n d) (S : Finset (Fin d)) :
    SimpleGraph (Fin n ⊕ Fin d) where
  Adj u v :=
    match u, v with
    | Sum.inl i, Sum.inr m => m ∈ S ∧ i ∈ N.A m
    | Sum.inr m, Sum.inl i => m ∈ S ∧ i ∈ N.A m
    | _, _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> simp_all⟩
  loopless := ⟨fun u h => by cases u <;> simp_all⟩

/-- The matching network graph `𝒢` (§2, p. 8): the simple bipartite graph whose vertices are the
agent types and the matches, with an edge between type `i` and match `m` iff `i ∈ 𝒜(m)`. -/
def networkGraph (N : MatchingNetwork n d) : SimpleGraph (Fin n ⊕ Fin d) :=
  incidenceGraph N Finset.univ

/-- The leaves of a graph on `Fin n ⊕ Fin d`: the vertices of degree exactly one. -/
noncomputable def leaves (G : SimpleGraph (Fin n ⊕ Fin d)) : Finset (Fin n ⊕ Fin d) := by
  classical
  exact Finset.univ.filter (fun v => G.degree v = 1)

/-- The number `∑_{m ∈ ℳ} M_{im}` of matches in which agent type `i` participates. -/
def matchCount (N : MatchingNetwork n d) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun m => i ∈ N.A m)).card

end ConstRegretMatch.Acyclic


