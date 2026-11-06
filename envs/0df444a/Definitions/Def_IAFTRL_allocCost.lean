-- Prove2me | Definitions.Def_IAFTRL_allocCost
-- name    : IAFTRL_allocCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:40.758724+00:00
-- url     : https://prove2.me/theorems/df1f7c9a-cdd3-4b72-b588-66dc87468dcb
-- title:
--   Information-acquisition cost $c^n(\mathcal A,\theta)$
-- statement:
--   For an allocation $n\in\mathbb R^{\mathcal A}$ and a loss vector $\theta$ with optimal action $a^*$, the **information-acquisition cost** of $n$ is
--   $$
--   c^n(\mathcal A,\theta)=\sum_{a\in\mathcal A}n_a\,\Delta(a),\qquad \Delta(a)=(a-a^*)^\top\theta .
--   $$
--   It is the regret paid by sampling according to $n$; $c^*(\mathcal A,\theta)$ is its infimum over feasible allocations.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.6

import Mathlib

namespace IAFTRL

open Matrix

/-- **Information-acquisition cost `c^n(𝒜, θ)`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.6: "`c^n(𝒜, θ) :=
Σ_{a∈𝒜} n_a Δ(a)` … call `c^n(𝒜, θ)` the information-acquisition cost of `n`", with the loss gap
`Δ(a) = (a − a*)^⊤θ` of p.6.

`allocCost arms θ jstar n = Σ_j n_j (a_j − a_{jstar})^⊤θ`. -/
def allocCost {d K : ℕ} (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar : Fin K)
    (n : Fin K → ℝ) : ℝ :=
  ∑ j, n j * ((arms j - arms jstar) ⬝ᵥ θ)

end IAFTRL


