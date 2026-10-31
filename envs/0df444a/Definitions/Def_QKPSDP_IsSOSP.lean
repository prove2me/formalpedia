-- Prove2me | Definitions.Def_QKPSDP_IsSOSP
-- name    : QKPSDP_IsSOSP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:24.147913+00:00
-- url     : https://prove2.me/theorems/4352d26b-e512-49c8-b638-72dbe02e4512
-- title:
--   Second-order stationary points of (SQKELR) (p.12 and Definition 4.5)
-- statement:
--   $R \in \mathcal K_{n,r}$ is a **second-order stationary point** of (SQKELR) if one of the following holds.
--
--   1. $R$ is regular and satisfies the first- and second-order KKT conditions: some $(\mu,\lambda)$ satisfies (32) and (33) for all $H$ in the tangent space (34) (p.12, Theorems 12.1 and 12.5 of Nocedal–Wright).
--   2. (Definition 4.5) $R = ve_1^\top \in \mathcal N_{n,r}$ with $v \in \{0,1\}^n$, and the optimal value of the SDP (29) is nonnegative:
--   $$
--   \bigl\langle 2\operatorname{diag}((Cv)\circ d) - C,\ X\bigr\rangle \ge 0 \quad\text{for every feasible } X \text{ of (29)}.
--   $$
--
--   By Proposition 3.1 the two cases are the regular and the non-regular points of $\mathcal K_{n,r}$. The second case is how the paper avoids assuming LICQ.
--
--   **Formalization Note** Definition 4.5's standing assumption $r \ge 3$ is a hypothesis of every theorem that uses this predicate.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, p.12; Definition 4.5, p.13; (31)–(34), p.14

import Mathlib
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_N
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_KKT1
import Definitions.Def_QKPSDP_KKT2
import Definitions.Def_QKPSDP_obj29
import Definitions.Def_QKPSDP_IsFeasible29

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, second-order stationary point of (SQKELR), p.12 and
Definition 4.5, p.13. `R ∈ K_{n,r}` and one of:

1. (p.12, (31)–(34), p.14) `R` is regular and satisfies the first- and second-order KKT
   conditions: some `(μ, λ)` satisfies (32) and (33) over the tangent space (34);
2. (Definition 4.5) `R = ve₁⊤ ∈ N_{n,r}` with `v ∈ {0,1}ⁿ`, and "the optimal function value of
   the SDP (29) is nonnegative": `⟨2diag((Cv) ∘ d) − C, X⟩ ≥ 0` for every feasible `X` of (29).

**Formalization Note** By Proposition 3.1 the two cases are the regular and the non-regular
points of `K_{n,r}`. "Optimal value ≥ 0" is "every feasible point has objective ≥ 0", which is
the same as the infimum being `≥ 0` (also when (29) is infeasible, value `+∞`). Definition 4.5's
standing `r ≥ 3` is a hypothesis of every theorem that uses this predicate. -/
def IsSOSP {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  R ∈ K a τ ∧
    ((IsRegular a τ R ∧ ∃ (μ : Fin n → ℝ) (lam : ℝ), KKT1 C a τ R μ lam ∧ KKT2 C a τ R μ lam) ∨
      (R ∈ N a τ ∧ ∃ v : Fin n → ℝ, (∀ i, v i = 0 ∨ v i = 1) ∧ R = vecMulVec v (e1 r) ∧
        ∀ X : Matrix (Fin n) (Fin n) ℝ, IsFeasible29 a τ v X → 0 ≤ (obj29 C v * Xᵀ).trace))

end QKPSDP


