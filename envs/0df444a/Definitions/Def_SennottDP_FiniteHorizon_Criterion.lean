-- Prove2me | Definitions.Def_SennottDP_FiniteHorizon_Criterion
-- name    : SennottDP_FiniteHorizon_Criterion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T06:15:54.234546+00:00
-- url     : https://prove2.me/theorems/3c0f22e3-b5f6-46ae-9510-f03bc9c2181f
-- title:
--   Finite horizon expected discounted cost, value function, optimal policies and the sets $B_i(\alpha,n)$
-- statement:
--   Fix an MDC $\Delta$, a nonnegative finite terminal cost $F : S \to [0,\infty)$ and a discount factor $\alpha$. For a policy $\theta$ and an initial state $i$, let $P_\theta(X_t = j, A_t = a \mid X_0 = i)$ be the probability that at time $t$ the state is $j$ and the action is $a$ (the sum over all histories $h_t$ ending in $j$ of $P_\theta(h_t)\,\theta(a \mid h_t)$). The expected cost at time $t$ is (2.6)
--   $$
--   E_\theta[C(X_t,A_t) \mid X_0 = i] = \sum_{j} \sum_{a \in A_j} C(j,a)\, P_\theta(X_t = j, A_t = a \mid X_0 = i).
--   $$
--   The **$n$ horizon expected discounted cost** of $\theta$ is (2.9)
--   $$
--   v_{\theta,\alpha,n}(i) = \sum_{t=0}^{n-1} \alpha^t E_\theta[C(X_t,A_t) \mid X_0 = i] + \alpha^n E_\theta[F(X_n) \mid X_0 = i],
--   $$
--   so that $v_{\theta,\alpha,0} = F$, and the **$n$ horizon value function** is (2.10) $v_{\alpha,n}(i) = \inf_\theta v_{\theta,\alpha,n}(i)$, the infimum over all policies. Both may equal $+\infty$ (Remark 2.4.2). A policy $\theta$ is **optimal for the $n$ horizon** (Definition 2.4.1) if $v_{\theta,\alpha,n}(i) = v_{\alpha,n}(i)$ for every $i \in S$.
--
--   For $n \ge 1$ the auxiliary function (3.1) and the set of minimizing actions are
--   $$
--   u_{\alpha,n}(i,a) = C(i,a) + \alpha \sum_j P_{ij}(a)\, v_{\alpha,n-1}(j), \qquad B_i(\alpha,n) = \{ b \in A_i : u_{\alpha,n}(i,b) = \min_{a \in A_i} u_{\alpha,n}(i,a) \}.
--   $$
--
--   These are the quantities the finite horizon optimality equation relates.
--
--   **Formalization Note** All costs and values live in $[0,\infty]$ (`ℝ≥0∞`), so sums and infima are those of the extended half-line, with $0 \cdot \infty = 0$; costs $C$ and $F$ are finite (`ℝ≥0`). The discount factor is a nonnegative real; every theorem assumes $0 < \alpha \le 1$ ($\alpha = 1$ is the undiscounted criterion (2.11)). The auxiliary function is written with $v_{\alpha,n-1}$ and is only used for $n \ge 1$. The minimum over $A_i$ is `Finset.inf'` over the finite nonempty set $A_i$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 23, Eq. (2.6); pp. 24–25, Eqs. (2.9)–(2.10), Definition 2.4.1, Remark 2.4.2; p. 36, Eq. (3.1) and B_i(α, n)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC

open scoped ENNReal NNReal
open Classical

namespace SennottDP.FiniteHorizon

namespace MDC

variable {S Act : Type} {M : MDC S Act}

/-- `P_θ(X_t = j, A_t = a | X_0 = i)`, the joint law of the state and the action at time `t`
(§2.3, pp. 22–23): the sum, over all histories `h_t` ending in `j`, of `P_θ(h_t) θ(a | h_t)`. -/
noncomputable def stateActionProb (θ : M.Policy) (i : S) (t : ℕ) (j : S) (a : Act) : ℝ≥0∞ :=
  ∑' h : List (S × Act), histProb θ i t h j * θ.σ h j a

/-- `P_θ(X_t = j | X_0 = i)`, the law of the state at time `t`. -/
noncomputable def stateProb (θ : M.Policy) (i : S) (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' h : List (S × Act), histProb θ i t h j

/-- The statistical average cost at time `t`, equation (2.6), p. 23:
`E_θ[C(X_t, A_t) | X_0 = i] = ∑_j ∑_{a ∈ A_j} C(j, a) P_θ(X_t = j, A_t = a | X_0 = i)`. -/
noncomputable def expectedCost (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' j : S, ∑ a ∈ M.A j, (M.C j a : ℝ≥0∞) * stateActionProb θ i t j a

/-- The expected terminal cost `E_θ[F(X_t) | X_0 = i] = ∑_j F(j) P_θ(X_t = j | X_0 = i)`. -/
noncomputable def expectedTerminal (F : S → ℝ≥0) (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' j : S, (F j : ℝ≥0∞) * stateProb θ i t j

/-- The `n` horizon expected discounted cost under `θ` with terminal cost `F`, equation (2.9),
p. 25: `v_{θ,α,n}(i) = ∑_{t=0}^{n-1} α^t E_θ[C(X_t,A_t) | X_0 = i] + α^n E_θ[F(X_n) | X_0 = i]`,
with values in `[0, ∞]` (Remark 2.4.2). For `n = 0` it is `F(i)`. -/
noncomputable def horizonCost (F : S → ℝ≥0) (α : ℝ≥0) (θ : M.Policy) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, (α : ℝ≥0∞) ^ t * expectedCost θ i t
    + (α : ℝ≥0∞) ^ n * expectedTerminal F θ i n

variable (M)

/-- The `n` horizon expected discounted value function, equation (2.10), p. 25:
`v_{α,n}(i) = inf_θ v_{θ,α,n}(i)`, the infimum over all general policies, in `[0, ∞]`. -/
noncomputable def value (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : M.Policy, horizonCost F α θ n i

/-- Definition 2.4.1, p. 25: `θ` is optimal for the `n` horizon if `v_{θ,α,n}(i) = v_{α,n}(i)`
for every state `i`. -/
def IsOptimal (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (θ : M.Policy) : Prop :=
  ∀ i, horizonCost F α θ n i = M.value F α n i

/-- The auxiliary function (3.1), p. 36, for `n ≥ 1`:
`u_{α,n}(i, a) = C(i, a) + α ∑_j P_ij(a) v_{α,n-1}(j)`. (It is only used with `n ≥ 1`.) -/
noncomputable def aux (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, M.P i a j * M.value F α (n - 1) j

/-- The set of minimizing actions, p. 36:
`B_i(α, n) = {b ∈ A_i | u_{α,n}(i, b) = min_{a ∈ A_i} u_{α,n}(i, a)}`. -/
noncomputable def minSet (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) : Finset Act :=
  (M.A i).filter
    (fun b => M.aux F α n i b = (M.A i).inf' (M.A_nonempty i) (M.aux F α n i))

end MDC

end SennottDP.FiniteHorizon


