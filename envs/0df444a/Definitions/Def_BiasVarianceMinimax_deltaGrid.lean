-- Prove2me | Definitions.Def_BiasVarianceMinimax_deltaGrid
-- name    : BiasVarianceMinimax_deltaGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:00.363152+00:00
-- url     : https://prove2.me/theorems/1b146ab3-1f0a-44ae-af82-234023a61754
-- title:
--   The two grids of tuning parameters
-- statement:
--   With $\alpha=1/(2(q_1+q_2))$ and a fixed $n_0\in\mathbb N$, the mission uses two grids of tuning parameters.
--
--   1. The baseline uses one value per budget: $\delta=d(n+n_0)^{-\alpha}$.
--   2. The weighted estimator uses one value per run: $\delta_j=\tilde d(j+n_0)^{-\alpha}$, $j=1,\dots,n$, which does not depend on the budget.
--
--   The first grid is `baselineDelta`, the second is `deltaGrid`, and `alpha` is $\alpha$.
--
--   **Formalization Note** Runs are indexed from $0$ in Lean: the index $i$ is run $j=i+1$, and `runPoint n₀ i` is the real number $j+n_0=i+1+n_0\ge 1$. "Any fixed integer" $n_0$ is read as $n_0\in\mathbb N$.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, §4.2, p.11; §5, p.19

import Mathlib

namespace BiasVarianceMinimax

/-- The exponent `α = 1/(2(q₁+q₂))`. Lam, Zhang & Zhang, arXiv:1902.04673v1, p.8 and p.11. -/
noncomputable def alpha (q₁ q₂ : ℝ) : ℝ := 1 / (2 * (q₁ + q₂))

/-- The real number `j + n₀` attached to run `j` of the paper, for the zero-based index `i = j - 1`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, (21), p.19.

**Formalization Note.** Runs are indexed by `Fin n`, so `i : Fin n` is run `j = i + 1` of the paper
and `j + n₀` is `i + 1 + n₀`. "Any fixed integer" `n₀` is read as `n₀ ∈ ℕ`, so this number is `≥ 1`. -/
noncomputable def runPoint (n₀ i : ℕ) : ℝ := (i : ℝ) + 1 + (n₀ : ℝ)

/-- The tuning parameter `δ = d (n + n₀)^(-α)` of the baseline, one value per budget `n`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, §4.2, p.11. -/
noncomputable def baselineDelta (q₁ q₂ : ℝ) (n₀ : ℕ) (d : ℝ) (n : ℕ) : ℝ :=
  d * ((n : ℝ) + (n₀ : ℝ)) ^ (-alpha q₁ q₂)

/-- The tuning parameter `δⱼ = d̃ (j + n₀)^(-α)` of run `j`, which depends on the run and not on the
budget. Lam, Zhang & Zhang, arXiv:1902.04673v1, §5, p.19; `i` is the zero-based index of `runPoint`. -/
noncomputable def deltaGrid (q₁ q₂ : ℝ) (n₀ : ℕ) (dTilde : ℝ) (i : ℕ) : ℝ :=
  dTilde * runPoint n₀ i ^ (-alpha q₁ q₂)

end BiasVarianceMinimax


