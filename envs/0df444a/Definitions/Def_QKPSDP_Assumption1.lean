-- Prove2me | Definitions.Def_QKPSDP_Assumption1
-- name    : QKPSDP_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:46.497017+00:00
-- url     : https://prove2.me/theorems/b68bd89c-1a35-4599-8ea1-ab4411421157
-- title:
--   Assumption 1 — $0 < a_i < \tau$ and $e^\top a > \tau$
-- statement:
--   Let $n$ be the number of items, $a \in \mathbb R^n$ the weight vector and $\tau \in \mathbb R$ the capacity. The pair $(a,\tau)$ satisfies **Assumption 1** if
--
--   $$
--   0 < a_i < \tau \quad (i \in [n]) \qquad\text{and}\qquad e^\top a = \sum_{i=1}^n a_i > \tau ,
--   $$
--
--   where $e$ is the all-ones vector, in the paper's standing setting $n > 1$.
--
--   Every item is lighter than the knapsack and the items together do not fit, which excludes trivial knapsack instances. Every result of the mission assumes it.
--
--   **Formalization Note** The clause $n > 1$ is the standing assumption of p.1 ("We consider the nontrivial case where $n > 1$"). For $n \ge 1$ it already follows from the other two clauses; it only excludes $n = 0$, where the printed condition would hold for every $\tau < 0$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Assumption 1, p.1 (with the standing "n > 1" of p.1)

import Mathlib

namespace QKPSDP

/-- Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack
problem, arXiv:2303.06599v1, Assumption 1, p.1: "The weight vector `a ∈ ℝⁿ` and capacity `τ ∈ ℝ`
satisfy the condition that for any `i ∈ [n]`, `0 < aᵢ < τ` and `e⊤a > τ`, where `e` is the vector
of all ones", in the paper's standing setting "We consider the nontrivial case where `n > 1`"
(p.1).

**Formalization Note** `e⊤a` is `∑ i, a i`; `[n]` is `Fin n` (indices from 0). The conjunct
`1 < n` is the standing assumption of p.1. For `n ≥ 1` it is implied by the other two clauses
(`n = 1` would need `a₀ < τ < a₀`); it only excludes `n = 0`, where the printed Assumption 1
holds for every `τ < 0` and, e.g., the SDP (29) has no feasible point (no `0 × 0` matrix has
trace 1). -/
def Assumption1 {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) : Prop :=
  1 < n ∧ (∀ i, 0 < a i ∧ a i < τ) ∧ τ < ∑ i, a i

end QKPSDP


