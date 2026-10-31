-- Prove2me | Definitions.Def_MPBSelect_feasibleSet
-- name    : MPBSelect_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:41.002984+00:00
-- url     : https://prove2.me/theorems/1e3ecb7a-49ac-4132-9290-7866cd2ea01c
-- title:
--   Feasible allocations of (8) and (20), the $kB$-simplex
-- statement:
--   A **static sampling allocation** is a vector $\boldsymbol\alpha=\{\alpha_i(\theta_b)\}_{1\le i\le k,\,1\le b\le B}$, where $\alpha_i(\theta_b)$ is the fraction of the simulation budget spent on the solution–parameter pair $(i,\theta_b)$. The feasible allocations of problems (8) and (20) are those with
--   $$
--   \sum_{i=1}^k\sum_{b=1}^B\alpha_i(\theta_b)=1,\qquad \alpha_i(\theta_b)\ge0\quad(1\le i\le k,\ 1\le b\le B).
--   $$
--   Zero ratios are allowed.
--
--   **Formalization Note** `α i b` is $\alpha_i(\theta_b)$, with `α : Fin k → Fin B → ℝ`.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4, p.11, (8); §4.2, p.17, (20)

import Mathlib

namespace MPBSelect

/-- **Feasible allocations of problems (8) and (20).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, (8), p.11 and (20),
p.17: "Σ_{i=1}^k Σ_{b=1}^B αi(θb) = 1, αi(θb) ≥ 0, 1 ≤ i ≤ k, 1 ≤ b ≤ B".

The set of sampling-ratio vectors `α = {α_i(θ_b)}` in the `kB`-simplex.

**Formalization Note** `α i b = α_i(θ_b)` with `i : Fin k`, `b : Fin B`. -/
def feasibleSet (k B : ℕ) : Set (Fin k → Fin B → ℝ) :=
  {α | ∑ i, ∑ b, α i b = 1 ∧ ∀ i b, 0 ≤ α i b}

end MPBSelect


