-- Prove2me | Definitions.Def_ReviewProvision_IsOptimal
-- name    : ReviewProvision_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:56:37.693997+00:00
-- url     : https://prove2.me/theorems/3816ece4-3edb-4f50-9338-2a14ab93786a
-- title:
--   Feasible sales and optimality for a policy
-- statement:
--   Sales $\vec k$ are **feasible** when $k_n\ge0$ for every cluster. They are **optimal for a policy** $\psi$ when they are feasible and $\Pi_\psi(\vec k')\le\Pi_\psi(\vec k)$ for every feasible $\vec k'$.
--
--   **Formalization Note** The paper does not state the feasible set; its proofs use $k_N\ge0$ and evaluate at $k_N=0$ (pp.37, 44). There is no upper bound: (27) is an equality without a multiplier, and sales above $1$ mean a negative first-period price. Optima are maximizers, so a statement about $\Pi^*_\psi$ asserts attainment.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), (6), p.15; pp.37, 44–45

import Mathlib
import Definitions.Def_ReviewProvision_profit

namespace ReviewProvision

/-- **Feasible first-period sales**: `k_n ≥ 0` for every cluster.

**Formalization Note.** The paper never states the feasible set. Its proofs use `k_N ≥ 0` and evaluate
at `k_N = 0` (pp.37, 44). There is no upper bound: (27), p.45, is an equality with no multiplier,
and the range of Lemma 9 can pass `1`. A sales volume above `1` is a negative first-period price. -/
def Feasible {N : ℕ} (k : Fin N → ℝ) : Prop := ∀ n, 0 ≤ k n

/-- **`~k` is optimal for policy `ψ`**: it is feasible and it maximizes `Π_ψ` over feasible sales.
SSRN 3403322 (manuscript of 2021-05-24), (6), p.15 (PDF 15).

**Formalization Note.** Optima are maximizers, not a supremum over `~k`, so a statement about `Π*_ψ`
states attainment. -/
def IsOptimal {N : ℕ} (p : Params) (ψ : Policy) (k : Fin N → ℝ) : Prop :=
  Feasible k ∧ ∀ k' : Fin N → ℝ, Feasible k' → profit p ψ k' ≤ profit p ψ k

end ReviewProvision


