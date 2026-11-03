-- Prove2me | Definitions.Def_WeightedCongestionBR_smoothSet
-- name    : WeightedCongestionBR_smoothSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:39.266597+00:00
-- url     : https://prove2.me/theorems/4495dc6c-1574-4133-8b12-b32952c07dfe
-- title:
--   Feasible smoothness values of Lemma 2
-- statement:
--   For $d$ and $\rho$, the set of values $\lambda\rho/(1-\mu\rho)$ over all pairs $\lambda\in\mathbb R$, $\mu\in(0,1/\rho)$ such that
--
--   $$
--   y\,f(z+x+y)\le \lambda\, y\, f(z+y)+\mu\, x\, f(z+x)\qquad\text{for all } x,y,z\ge 0,\ f\in\mathfrak P_d .
--   $$
--
--   Its infimum is the constant $B$ of Lemma 2, which equals $\Phi_{d,\rho}^{d+1}$.
--
--   **Formalization Note** $\lambda$ is written `lam`.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 2, p.7

import Mathlib
import Definitions.Def_WeightedCongestionBR_IsPd
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The set whose infimum is the constant `B` of Lemma 2 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Lemma 2, p.7): the values
`λρ / (1 − μρ)` over all `λ ∈ ℝ`, `μ ∈ (0, 1/ρ)` such that
`y f(z + x + y) ≤ λ y f(z + y) + μ x f(z + x)` for all `x, y, z ≥ 0` and `f ∈ 𝔓_d`.

**Formalization Note** `λ` is written `lam` (a reserved token in Lean). -/
def smoothSet (d : ℕ) (ρ : ℝ) : Set ℝ :=
  {B | ∃ lam μ : ℝ, 0 < μ ∧ μ < 1 / ρ ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → ∀ f : Polynomial ℝ, IsPd d f →
      y * f.eval (z + x + y) ≤ lam * y * f.eval (z + y) + μ * x * f.eval (z + x)) ∧
    B = lam * ρ / (1 - μ * ρ)}

end WeightedCongestionBR


