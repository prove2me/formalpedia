-- Prove2me | Definitions.Def_QKPSDP_N
-- name    : QKPSDP_N
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:11.709046+00:00
-- url     : https://prove2.me/theorems/ca4b4b51-742f-4ddf-87ce-4f74773cb3e0
-- title:
--   The set $\mathcal N_{n,r}$ of non-regular points
-- statement:
--   $$
--   \mathcal N_{n,r} := \{0_{n\times r}\} \sqcup \bigl\{ v e_1^\top : v \in \{0,1\}^n,\ a^\top v = \tau \bigr\}. \qquad (4)
--   $$
--
--   Here $ve_1^\top$ is the $n\times r$ matrix whose first column is $v$ and whose other columns vanish. Proposition 3.1 shows that $\mathcal N_{n,r}$ is exactly the set of non-regular points of $\mathcal K_{n,r}$; its nonzero elements correspond to the binary knapsack solutions that fill the capacity exactly.
--
--   **Formalization Note** The disjoint union is written as a union; the two parts are disjoint when $\tau \neq 0$, in particular under Assumption 1.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Proposition 3.1, (4), p.6

import Mathlib
import Definitions.Def_QKPSDP_e1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Proposition 3.1, (4), p.6:
`N_{n,r} := {0_{n×r}} ⊔ { ve₁⊤ : v ∈ {0,1}ⁿ, a⊤v = τ }`.

**Formalization Note** `ve₁⊤` is `vecMulVec v e₁` (the `n × r` matrix whose first column is `v`
and whose other columns vanish); `v ∈ {0,1}ⁿ` is `∀ i, v i = 0 ∨ v i = 1`. The paper's disjoint
union `⊔` is written `∪`: the two parts are disjoint whenever `τ ≠ 0` (then `v ≠ 0`), in
particular under Assumption 1. -/
def N {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) : Set (Matrix (Fin n) (Fin r) ℝ) :=
  {0} ∪ {R | ∃ v : Fin n → ℝ, (∀ i, v i = 0 ∨ v i = 1) ∧ a ⬝ᵥ v = τ ∧ R = vecMulVec v (e1 r)}

end QKPSDP


