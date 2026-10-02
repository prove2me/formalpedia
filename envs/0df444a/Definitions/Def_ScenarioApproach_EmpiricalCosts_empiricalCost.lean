-- Prove2me | Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
-- name    : ScenarioApproach_EmpiricalCosts_empiricalCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T17:56:37.707991+00:00
-- url     : https://prove2.me/theorems/2a2667a5-a06f-410c-bb0f-fd1130a2e1ac
-- title:
--   Definition 8.1 — empirical costs
-- statement:
--   Let $\nu$ be a decision and $(\delta_1,\dots,\delta_m)$ a sample of scenarios. Consider the cost values $\ell(\nu,\delta_i)$, $i=1,\dots,m$, and sort them in decreasing order,
--
--   $$
--   \ell^*_1\ \ge\ \ell^*_2\ \ge\ \cdots\ \ge\ \ell^*_m .
--   $$
--
--   The value $\ell^*_k$, the $k$-th largest of the costs (counted with multiplicity), is the $k$-th **empirical cost**. The book takes $\nu=\nu^*$, the solution of the scenario program; then $\ell^*_1=\ell^*$ is its optimal value.
--
--   Empirical costs record how the costs of the sampled scenarios spread below the worst case, information that the optimal value alone discards.
--
--   **Formalization Note** `kthLargest c k` is the $k$-th largest entry of a finite real tuple `c : Fin m → ℝ`, with $k$ counted from $1$ as in the book; it reads position $m-k$ of the increasing rearrangement `Tuple.sort c` (checked on $(5,1,3)$: $k=1,2,3$ give $5,3,1$). Ties are allowed. Outside $1\le k\le m$ the value is the junk $0$ and is never used. `empiricalCost ℓ ω ν k` applies this to the costs $\ell(\nu,\delta_i)$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90, Definition 8.1

import Mathlib

namespace ScenarioApproach.EmpiricalCosts

/-- The `k`-th largest entry (`k` 1-based) of a finite list of reals `c 0, …, c (m-1)`:
`kthLargest c 1 ≥ kthLargest c 2 ≥ ⋯ ≥ kthLargest c m`. `Tuple.sort c` sorts `c` increasingly,
so the `k`-th largest entry sits at position `m - k` of the sorted list. Outside `1 ≤ k ≤ m` the
value is the junk `0`. -/
noncomputable def kthLargest {m : ℕ} (c : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ m then c (Tuple.sort c ⟨m - k, by omega⟩) else 0

/-- Definition 8.1 (empirical costs). The cost values `ℓ(ν, δᵢ)`, `i = 1, …, m`, achieved by the
decision `ν` on the scenarios `δᵢ = ω (i-1)`, sorted in decreasing order: `empiricalCost ℓ ω ν k`
is `ℓ*_k`, the `k`-th largest of them (`1 ≤ k ≤ m`). The book takes `ν = ν*`. -/
noncomputable def empiricalCost {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  kthLargest (fun i => ℓ ν (ω i)) k

end ScenarioApproach.EmpiricalCosts


