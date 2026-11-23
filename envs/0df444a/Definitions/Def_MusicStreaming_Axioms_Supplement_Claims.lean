-- Prove2me | Definitions.Def_MusicStreaming_Axioms_Supplement_Claims
-- name    : MusicStreaming_Axioms_Supplement_Claims
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:25:12.810444+00:00
-- url     : https://prove2.me/theorems/2a8008b5-eab5-4c11-8e98-2660785a164f
-- title:
--   §5, pp. 15–16 — claims problems, issue totals, weight functions and the weighted proportional rule
-- statement:
--   A **claims problem** (Ju et al., 2007) is a tuple $(N,K,c,E)$: a finite set $N$ of agents, a finite set $K$ of issues, characteristics $c=(c_{ij})_{i\in N,j\in K}$, where $c_{ij}$ is the characteristic of agent $i$ on issue $j$, and an amount $E$ to be divided. It is *valid* when $c_{ij}\ge0$ for all $i\in N$, $j\in K$ and $E\in\mathbb R_+$. A **rule** assigns a vector $R(N,K,c,E)\in\mathbb R^N$ to every claims problem. For each issue $j\in K$ write $c_{\cdot j}=(c_{ij})_{i\in N}$ and $C^j=\sum_{i\in N}c_{ij}$.
--
--   A **weight function** $\omega:\mathbb R^K_+\times\mathbb R_+\to\mathbb R^K_+$ assigns to the issue totals and the amount a probability distribution over the issues: for every nonempty finite set of issues $K$, every $C\in\mathbb R^K_+$ and every $E\ge0$, $0\le\omega_j(C,E)\le1$ for all $j\in K$ and $\sum_{j\in K}\omega_j(C,E)=1$. The **weighted proportional rule** associated to $\omega$ assigns to each $i\in N$
--
--   $$P^\omega_i(N,K,c,E)=\sum_{j\in K}\frac{c_{ij}}{C^j}\,\omega_j\big((C^j)_{j\in K},E\big)\,E .$$
--
--   It applies the proportional rule to each single-issue subproblem and averages the results with the weights $\omega_j$. This family is the one used in Theorem 4(a) to represent the pro-rata and user-centric rewards.
--
--   **Formalization Note** A weight function is a family indexed by the finite issue set $K$; it is required to read the totals $C$ only through $(C^j)_{j\in K}$, and its probability-vector property is required for nonempty $K$ (for $K=\emptyset$ the rule is the empty sum $0$). When some $C^j=0$, Lean's $x/0=0$ makes that issue's term $0$; this does not occur for problems derived from streaming data, where $C^j\ge1$.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 15–16, §5 (claims problem, weight function, weighted proportional rule)

import Mathlib

namespace MusicStreaming.Axioms.Supplement

/-- A claims problem `(N, K, c, E)` (§5, p. 15, after Ju et al. 2007): a finite set `N` of
agents, a finite set `K` of issues, characteristics `c i j` (`c_ij`, agent `i` on issue `j`) and
an amount `E` to be divided. Only the values of `c` on `N × K` matter. -/
structure ClaimsProblem (α κ : Type*) where
  /-- the agents -/
  N : Finset α
  /-- the issues -/
  K : Finset κ
  /-- the characteristics `c_ij` -/
  c : α → κ → ℝ
  /-- the amount to be divided -/
  E : ℝ

variable {α κ : Type*}

/-- The data of a claims problem as on p. 15: `c_ij ≥ 0` for `i ∈ N`, `j ∈ K`, and `E ∈ ℝ_+`. -/
def ClaimsProblem.IsValid (P : ClaimsProblem α κ) : Prop :=
  (∀ i ∈ P.N, ∀ j ∈ P.K, 0 ≤ P.c i j) ∧ 0 ≤ P.E

/-- A rule assigns a real vector over the agents to every claims problem (p. 15). -/
abbrev ClaimsRule (α κ : Type*) := ClaimsProblem α κ → α → ℝ

/-- The issue totals `C^j = ∑_{i ∈ N} c_ij` (p. 15). -/
def ClaimsProblem.issueTotal (P : ClaimsProblem α κ) (j : κ) : ℝ := ∑ i ∈ P.N, P.c i j

/-- A candidate weight function `ω` (p. 15): for a set of issues `K`, a vector of issue totals
`C` and an amount `E` it returns weights `ω_j(C, E)`. -/
abbrev WeightFunction (κ : Type*) := Finset κ → (κ → ℝ) → ℝ → κ → ℝ

/-- `ω : ℝ^K_+ × ℝ_+ → ℝ^K_+` is a weight function (pp. 15–16): for every nonempty finite set
of issues `K`, every `C ∈ ℝ^K_+` and every `E ∈ ℝ_+`, `ω(C, E)` is a probability distribution
on `K` (`0 ≤ ω_j(C, E) ≤ 1` for all `j ∈ K` and `∑_{j ∈ K} ω_j(C, E) = 1`), and `ω(C, E)`
depends on `C` only through its coordinates `(C^j)_{j ∈ K}`. -/
def IsWeightFunction (ω : WeightFunction κ) : Prop :=
  (∀ (K : Finset κ) (C : κ → ℝ) (E : ℝ), K.Nonempty → (∀ j ∈ K, 0 ≤ C j) → 0 ≤ E →
      (∀ j ∈ K, 0 ≤ ω K C E j ∧ ω K C E j ≤ 1) ∧ ∑ j ∈ K, ω K C E j = 1) ∧
  (∀ (K : Finset κ) (C C' : κ → ℝ) (E : ℝ), (∀ j ∈ K, C j = C' j) →
      ∀ j ∈ K, ω K C E j = ω K C' E j)

/-- The weighted proportional rule associated to `ω` (p. 16):
`P^ω_i(N, K, c, E) = ∑_{j ∈ K} (c_ij / C^j) · ω_j((C^j)_{j ∈ K}, E) · E`.
(For an issue with `C^j = 0`, Lean's `x / 0 = 0` makes its term `0`.) -/
noncomputable def weightedProportional (ω : WeightFunction κ) : ClaimsRule α κ :=
  fun P i => ∑ j ∈ P.K, P.c i j / P.issueTotal j * ω P.K P.issueTotal P.E j * P.E

end MusicStreaming.Axioms.Supplement


