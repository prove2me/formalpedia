-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_Network
-- name    : ConstRegretMatch_Upper_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:13.15905+00:00
-- url     : https://prove2.me/theorems/48f6aa31-1c26-4108-9231-9482d26939aa
-- title:
--   §2, p. 7 — the matching network topology 𝒜(m), the matching matrix M, arrival probabilities λ and match values r
-- statement:
--   A **matching network** has a finite set of agent types $\mathcal A=\{1,\dots,n\}$ and a finite set of matches $\mathcal M=\{1,\dots,d\}$. Each match $m$ is a set $\mathcal A(m)\subseteq\mathcal A$ of agent types; performing match $m$ once uses one agent of every type in $\mathcal A(m)$. The paper's two standing assumptions are part of the definition:
--
--   1. every match uses at least two agent types, $|\mathcal A(m)|\ge 2$;
--   2. every agent type participates in at least one match.
--
--   The **matching matrix** $M\in\{0,1\}^{n\times d}$ has $M_{im}=1$ if and only if $i\in\mathcal A(m)$.
--
--   Agents arrive one per period; an arrival is of type $i$ with probability $\lambda_i$, where
--   $$\lambda_i>0\ \text{for all } i,\qquad \sum_{i\in\mathcal A}\lambda_i=1.$$
--   Match $m$ generates a value $r_m>0$. The triple $\mathcal G=(M,\lambda,r)$ is the matching network of the paper.
--
--   These objects are the data of every statement of the mission.
--
--   **Formalization Note** Types are `Fin n` and matches `Fin d`, both 0-based: the paper's type $i$ is index $i-1$. The topology (the sets $\mathcal A(m)$ with the two standing assumptions) is the structure `MatchingNetwork n d`; $\lambda$ (written `lam`) and $r$ are separate vectors with the predicates `IsArrivalRates` and `IsMatchValues`, so that constants can be quantified after the topology and $r$ but before $\lambda$. The matrix $M$ is available both over $\mathbb N$ (`inc`) and over $\mathbb R$ (`M`).
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 7, §2 (Matching network and dynamics)

import Mathlib

namespace ConstRegretMatch.Upper

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

/-- The matching matrix `M ∈ {0,1}^{n×d}`, as natural numbers: `M i m = 1` iff `i ∈ 𝒜(m)`. -/
def MatchingNetwork.inc (N : MatchingNetwork n d) (i : Fin n) (m : Fin d) : ℕ :=
  if i ∈ N.A m then 1 else 0

/-- The matching matrix `M`, as a real matrix (rows: agent types, columns: matches). -/
noncomputable def MatchingNetwork.M (N : MatchingNetwork n d) : Matrix (Fin n) (Fin d) ℝ :=
  fun i m => (N.inc i m : ℝ)

/-- Arrival probabilities (§2, p. 7): `λ_i > 0` for every type and `∑_i λ_i = 1`.
(`lam` stands for `λ`, which is reserved in Lean.) -/
def IsArrivalRates (lam : Fin n → ℝ) : Prop :=
  (∀ i, 0 < lam i) ∧ ∑ i, lam i = 1

/-- Match values (§2, p. 7): `r_m > 0` for every match. -/
def IsMatchValues (r : Fin d → ℝ) : Prop :=
  ∀ m, 0 < r m

end ConstRegretMatch.Upper


