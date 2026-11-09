-- Prove2me | Definitions.Def_LinearChoresCLS_Psi
-- name    : LinearChoresCLS_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:33.636515+00:00
-- url     : https://prove2.me/theorems/a46078ac-d8d9-432c-a987-3f3d0b82c4a6
-- title:
--   The logarithmic objective $\Psi(p)=-\sum_a B_a\log\mu_a(p)$ (Eq. (2.3))
-- statement:
--   For a chores market with at least one chore and prices $p$, the **optimal price-to-disutility ratio** of agent $a$ is
--   $$
--   \mu_a(p)=\max_{j\in M}\frac{p_j}{d_{aj}},
--   $$
--   and the **logarithmic objective** is
--   $$
--   \Psi(p)=-\sum_{a\in N}B_a\log\mu_a(p).
--   $$
--   Theorem 2.3 characterizes equilibrium prices as the points of the price domain satisfying the first-order conditions for maximizing $\Psi$; the reduction approximates a target quadratic by $\Psi$ along a family of prices.
--
--   **Formalization Note** The maximum is `Finset.sup'` over the nonempty finite chore type. `Real.log` is $0$ on nonpositive arguments; every statement evaluates $\Psi$ at strictly positive prices, where every $\mu_a(p)>0$.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 2.3, Eq. (2.3), p.7

import Mathlib
import Definitions.Def_LinearChoresCLS_ChoresMarket

open Finset

namespace LinearChoresCLS

namespace ChoresMarket

variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]

/-- **Optimal price-to-disutility ratio** `μ_a(p) := max_{j ∈ [m]} p_j / d_{aj}`
(arXiv:2611.06589, held version sha256 85d34a9e…, Theorem 2.3, Eq. (2.3), p.7).

**Formalization Note.** The maximum is `Finset.sup'` over the (nonempty, finite) chore type, so
`[Nonempty M]` is required; the paper has `m ≥ 1` chores. -/
noncomputable def mu (F : ChoresMarket N M) (a : N) (p : M → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => p j / F.disutil a j)

/-- **Logarithmic objective** `Ψ(p) := −∑_a B_a log μ_a(p)` (arXiv:2611.06589, Theorem 2.3,
Eq. (2.3), p.7), the objective whose first-order conditions over the price domain `P`
characterize equilibrium prices.

**Formalization Note.** `Real.log` returns `0` on nonpositive arguments; every statement using
`Psi` evaluates it at strictly positive prices, where every `μ_a(p) > 0`. -/
noncomputable def Psi (F : ChoresMarket N M) (p : M → ℝ) : ℝ :=
  -∑ a, F.earn a * Real.log (F.mu a p)

end ChoresMarket

end LinearChoresCLS


