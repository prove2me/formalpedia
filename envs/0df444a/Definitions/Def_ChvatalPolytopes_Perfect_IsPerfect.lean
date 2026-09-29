-- Prove2me | Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect
-- name    : ChvatalPolytopes_Perfect_IsPerfect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:12:34.050148+00:00
-- url     : https://prove2.me/theorems/0a736b93-4f61-4ed7-8dd9-bef0b492bc34
-- title:
--   Perfect ($\alpha$-perfect) graphs as a zero–one min–max (§3)
-- statement:
--   Let $G=(V,E)$ be a finite graph, $S(G)$ the incidence vectors of its stable sets and $C(G)$ the vertex sets of its maximal cliques. For $c\in\mathbb R^V$ write $cx=\sum_{u\in V}c_ux_u$.
--
--   $G$ is called **perfect** (or **$\alpha$-perfect**) if, for every zero–one valued vector $c=(c_u:u\in V)$,
--   $$\max\{cx : x\in S(G)\}=\min\Big\{\sum_{W\in C(G)}\lambda_W \;:\; \lambda_W\in\{0,1\},\ \sum_{W\in C(G),\,u\in W}\lambda_W\ge c_u \text{ for each } u\in V\Big\}.$$
--
--   If $c$ is the incidence vector of a set $A\subseteq V$, the left side is the largest size of a stable subset of $A$ and the right side is the least number of maximal cliques of $G$ covering $A$; perfection asks that these agree for every $A$. This is the notion of perfection in which Theorem 3.1 is stated.
--
--   **Formalization Note** The equality "max = min" is written out: there is a number $m$ such that $m$ is the maximum of $cx$ over $S(G)$ (attained, and an upper bound — the auxiliary predicate `IsStableMax`), some zero–one $\lambda$ satisfying the covering constraints has $\sum_W\lambda_W=m$, and every such $\lambda$ has $\sum_W\lambda_W\ge m$. The weights are functions `Finset V → ℝ` whose values are read only on $C(G)$; $c$ is a real vector with each $c_u\in\{0,1\}$. This is not Berge's $\chi(G_A)=\omega(G_A)$ definition.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 140, §3 (definition of perfect)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope

namespace ChvatalPolytopes.Perfect

/-- `m` is the maximum of `{cx : x ∈ S(G)}`: some stable-set incidence vector `x` has
`Σ_u c_u x_u = m`, and every one has `Σ_u c_u x_u ≤ m`. -/
def IsStableMax {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : V → ℝ)
    (m : ℝ) : Prop :=
  (∃ x ∈ stableVectors G, ∑ u, c u * x u = m) ∧ ∀ x ∈ stableVectors G, ∑ u, c u * x u ≤ m

/-- **Perfect** (or α-perfect) graph (Chvátal 1975, p. 140): for every zero–one valued vector
`c = (c_u : u ∈ V)`, the maximum of `{cx : x ∈ S(G)}` is equal to the minimum of
`{Σ (λ_W : W ∈ C(G)) : λ_W ∈ {0, 1} and, for each u ∈ V, Σ (λ_W : u ∈ W ∈ C(G)) ≥ c_u}`.

Here "max = min" is spelled out: there is a value `m` which is the maximum over `S(G)`, which is
attained by some zero–one `λ` covering `c`, and which is at most the objective of every such
`λ`. The weights `λ : Finset V → ℝ` are only read on `C(G) = maximalCliques G`. -/
def IsPerfect {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ c : V → ℝ, (∀ u, c u = 0 ∨ c u = 1) →
    ∃ m : ℝ, IsStableMax G c m ∧
      (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, lam W = 0 ∨ lam W = 1) ∧
        (∀ u, c u ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
        ∑ W ∈ maximalCliques G, lam W = m) ∧
      (∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, lam W = 0 ∨ lam W = 1) →
        (∀ u, c u ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
        m ≤ ∑ W ∈ maximalCliques G, lam W)

end ChvatalPolytopes.Perfect


