-- Prove2me | Definitions.Def_BernoulliPoA_prophetSmoothParams
-- name    : BernoulliPoA_prophetSmoothParams
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:58.825124+00:00
-- url     : https://prove2.me/theorems/6fb76180-2083-4c84-a85e-87251ca0e4e9
-- title:
--   $(\lambda,\mu,q)$-smoothness
-- statement:
--   The pairs $(\lambda,\mu)$ with $\lambda\ge 0$ and $\mu\in[0,1)$ such that
--   $$
--   \frac1q\,k\,c^q(1+m)\le\lambda\,k\,c(k)+\mu\,m\,c^q(m)\qquad\forall k,m\in\mathbb N,\ \forall c\in\mathcal C.
--   $$
--
--   The left side carries the expected cost of a deviation and the right side the cost of the prophet and of the current profile, so the condition sits between deterministic smoothness and smoothness of the costs $c^q$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (28), p.19

import Mathlib
import Definitions.Def_BernoulliPoA_binomExp

namespace BernoulliPoA

/-- **`(λ, μ, q)`-smoothness.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3.2, display (28), p.19: the pairs `(λ, μ)` with `λ ≥ 0`, `μ ∈ [0, 1)` such that
`(1/q) k c^q(1 + m) ≤ λ k c(k) + μ m c^q(m)` for all `k, m ∈ ℕ` and all `c ∈ C`. -/
def prophetSmoothParams (C : Set (ℕ → ℝ)) (q : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 < 1 ∧ ∀ c ∈ C, ∀ k m : ℕ,
    (1 / q) * k * binomExp c q (1 + m) ≤ x.1 * k * c k + x.2 * m * binomExp c q m}

end BernoulliPoA


