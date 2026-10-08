-- Prove2me | Definitions.Def_SongZipkinFluct_FixedCost_Policy
-- name    : SongZipkinFluct_FixedCost_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:35.3122+00:00
-- url     : https://prove2.me/theorems/b60a7199-7b66-45c2-91e0-997d30fba862
-- title:
--   (1) — the uniformized infinite-horizon problem: history-dependent policies, discounted policy cost, optimality and the world-dependent (r, S) policy
-- statement:
--   The infinite-horizon problem is the uniformized Markov decision process of the optimality equation (1). The state is $(i, x)$, the world state and the inventory position $x \in \mathbb Z$; a decision is an order-up-to level $y \ge x$. The cost until the next event of the uniformizing Poisson process is
--   $$
--   K\delta(y - x) + c(y - x) + \beta C(i, y),
--   $$
--   and the next state is $(i, y-1)$ with probability $\lambda_i/\mu$, $(j, y)$ with probability $q_{ij}/\mu$ ($j \ne i$), and $(i, y)$ with probability $1 - (\lambda_i + q_i)/\mu$; costs after each transition are discounted by $\gamma = \beta\mu$.
--
--   A **policy** $\sigma$ is a deterministic rule that chooses $y$ from the whole history of past states and the current state; it is **feasible** if it always chooses $y \ge x$. Its cost $V_\sigma(i, x)$ from the initial state $(i, x)$ is the expected total discounted cost, the supremum over $N$ of the expected discounted cost of the first $N$ decisions (all costs are nonnegative, so it is a value in $[0, \infty]$). A feasible policy is **optimal** if its cost from every initial state is at most the cost of every feasible policy.
--
--   The **world-dependent $(r, S)$ policy** with parameters $\{(r(i), S(i))\}_{i \in I}$ orders up to $S(i)$ if the inventory position $x$ satisfies $x \le r(i)$ while the world is in state $i$, and does not order otherwise.
--
--   **Formalization Note** Costs are valued in $[0, \infty]$ and the cost of a policy is a supremum of finite-horizon costs, so no integrability conditions arise. Randomized policies are not in the class; for nonnegative costs on a countable state space they cannot do better than deterministic history-dependent ones (the paper relies on Bertsekas and Shreve 1978, Props. 9.12 and 9.16). The class is not restricted to stationary or Markov policies.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 355, (1); p. 358, Theorem 3(b); p. 359, Theorem 5(e)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Model

open scoped ENNReal

namespace SongZipkinFluct.FixedCost

open Model

variable {I : Type*} [DecidableEq I]

/-- A deterministic, history-dependent ordering rule for the uniformized problem (1) (p. 355):
given the list of past states and the current state `(i, x)` (world state, inventory position),
it returns the order-up-to level `y`. Markov and stationary rules are the special cases that
ignore the history. -/
def Policy (I : Type*) := List (I × ℤ) → I × ℤ → ℤ

/-- A rule is feasible if it never orders a negative quantity: `y ≥ x` (p. 355). -/
def Policy.Feasible (σ : Policy I) : Prop := ∀ hist s, s.2 ≤ σ hist s

/-- The stage cost of (1) (p. 355) in state `(i, x)` under decision `y`:
`Kδ(y − x) + c(y − x) + βC(i, y)`, the discounted order cost plus the expected discounted
inventory cost until the next event of the uniformizing Poisson process. It is nonnegative for
`y ≥ x`; `ENNReal.ofReal` only matters for infeasible decisions. -/
noncomputable def stageCost (M : Model I) (K : ℝ) (s : I × ℤ) (y : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (K * SongZipkinFluct.Linear.delta (y - s.2) + M.c * ((y : ℝ) - (s.2 : ℝ)) + M.β * M.C s.1 y)

/-- The expectation of `V` over the next state after decision `y` in world state `i` (p. 355):
`(i, y − 1)` with probability `λ_i/μ`, `(j, y)` with probability `q_ij/μ` (`j ≠ i`), and `(i, y)`
with probability `1 − (λ_i + q_i)/μ`. -/
noncomputable def nextExp (M : Model I) (V : I × ℤ → ℝ≥0∞) (i : I) (y : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (M.lam i / M.μ) * V (i, y - 1)
    + (∑' j, if j = i then 0 else ENNReal.ofReal (M.Q i j / M.μ) * V (j, y))
    + ENNReal.ofReal (1 - (M.lam i + M.qrate i) / M.μ) * V (i, y)

/-- `cost M K σ N hist s`: the expected discounted cost of the first `N` decision epochs of the
uniformized problem (1) under the rule `σ`, from state `s` with past history `hist`; each
transition is discounted by `γ = βμ` (p. 355). -/
noncomputable def cost (M : Model I) (K : ℝ) (σ : Policy I) :
    ℕ → List (I × ℤ) → I × ℤ → ℝ≥0∞
  | 0, _, _ => 0
  | N + 1, hist, s =>
      stageCost M K s (σ hist s)
        + ENNReal.ofReal M.γ * nextExp M (fun s' => cost M K σ N (hist ++ [s]) s') s.1 (σ hist s)

/-- The infinite-horizon expected total discounted cost of `σ` from the initial state `s`
(empty history), `sup_N` of the `N`-epoch costs (all stage costs are nonnegative). -/
noncomputable def policyCost (M : Model I) (K : ℝ) (σ : Policy I) (s : I × ℤ) : ℝ≥0∞ :=
  ⨆ N : ℕ, cost M K σ N [] s

/-- `σ` is optimal for the infinite-horizon problem (1) with fixed cost `K`: it is feasible and,
from every initial state, its cost is no larger than that of any feasible deterministic
history-dependent rule.

Formalization Note: randomized rules are not in the class; for nonnegative costs on a countable
state space they cannot do better than deterministic history-dependent ones (the paper relies on
Bertsekas and Shreve 1978, Props. 9.12 and 9.16). -/
def IsOptimal (M : Model I) (K : ℝ) (σ : Policy I) : Prop :=
  σ.Feasible ∧ ∀ σ' : Policy I, σ'.Feasible → ∀ s, policyCost M K σ s ≤ policyCost M K σ' s

/-- The stationary world-dependent `(r, S)` policy (Theorem 3(b), p. 358): in state `(i, x)`,
order up to `S(i)` if `x ≤ r(i)`, otherwise do not order. -/
def rSPolicy (r S : I → ℤ) : Policy I := fun _ s => if s.2 ≤ r s.1 then S s.1 else s.2

end SongZipkinFluct.FixedCost


