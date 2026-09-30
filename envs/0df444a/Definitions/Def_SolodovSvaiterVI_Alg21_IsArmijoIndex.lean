-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_IsArmijoIndex
-- name    : SolodovSvaiterVI_Alg21_IsArmijoIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:11:36.101945+00:00
-- url     : https://prove2.me/theorems/d90368ed-5751-41e8-a6c4-72671ad0f800
-- title:
--   $k$ is the smallest nonnegative integer satisfying (2.1)
-- statement:
--   With $C$, $F$, $\gamma$, $\sigma$ and $x$ as in condition (2.1), a nonnegative integer $k$ is the **Armijo index** at $x$ if $k$ satisfies (2.1) and no smaller nonnegative integer does:
--
--   $$\langle F(x - \gamma^k r(x)), r(x) \rangle \ge \sigma \|r(x)\|^2 \quad\text{and}\quad \langle F(x - \gamma^j r(x)), r(x) \rangle < \sigma \|r(x)\|^2 \ \text{ for all } 0 \le j < k.$$
--
--   This is the index $k_i$ of Algorithm 2.1, whose stepsize is $\eta_i = \gamma^{k_i}$. Minimality matters: it is what prevents the stepsizes from being made arbitrarily small.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 767, Algorithm 2.1 ("k_i being the smallest nonnegative integer k satisfying (2.1)")

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds

namespace SolodovSvaiterVI.Alg21

/-- `k` is the smallest nonnegative integer satisfying the linesearch condition (2.1) at `x`
(Algorithm 2.1, Solodov–Svaiter, p. 767: "`kᵢ` being the smallest nonnegative integer `k`
satisfying (2.1)"). -/
def IsArmijoIndex {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (gamma sigma : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : Prop :=
  ArmijoHolds F C gamma sigma x k ∧ ∀ j < k, ¬ ArmijoHolds F C gamma sigma x j

end SolodovSvaiterVI.Alg21


