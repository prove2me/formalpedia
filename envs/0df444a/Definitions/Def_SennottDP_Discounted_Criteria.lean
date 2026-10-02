-- Prove2me | Definitions.Def_SennottDP_Discounted_Criteria
-- name    : SennottDP_Discounted_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T06:51:17.403452+00:00
-- url     : https://prove2.me/theorems/1eeda7d6-545c-4ca3-ba5d-c322ef07ae20
-- title:
--   Expected discounted costs $v_{\theta,\alpha,n}$, $V_{\theta,\alpha}$ and the value functions $v_{\alpha,n}$, $V_\alpha$
-- statement:
--   Fix an MDC and a policy $\theta$. Starting from the initial state $X_0 = i$, the policy and the transition probabilities determine the joint law of the states $X_t$ and actions $A_t$: the probability of the history $(i_0, a_0, \dots, a_{n-1}, i_n)$ is
--   $$\mathbf 1\{i_0 = i\} \prod_{t=0}^{n-1} \theta(a_t \mid h_t)\, P_{i_t i_{t+1}}(a_t).$$
--   The expected cost at time $t$ is $E_\theta[C(X_t,A_t) \mid X_0 = i] = \sum_j \sum_{a \in A_j} C(j,a) P_\theta(X_t = j, A_t = a \mid X_0 = i)$, and for $W : S \to [0,\infty]$ we write $E_\theta[W(X_n) \mid X_0 = i]$ for the expectation of $W$ at the state at time $n$.
--
--   For a discount factor $\alpha$:
--
--   1. the $n$-horizon expected discounted cost with terminal cost zero is $v_{\theta,\alpha,n}(i) = \sum_{t=0}^{n-1} \alpha^t E_\theta[C(X_t,A_t) \mid X_0 = i]$, and $v_{\alpha,n}(i) = \inf_\theta v_{\theta,\alpha,n}(i)$;
--   2. the infinite horizon expected discounted cost is
--   $$V_{\theta,\alpha}(i) = \sum_{t=0}^{\infty} \alpha^t E_\theta[C(X_t,A_t) \mid X_0 = i],$$
--   and the discounted value function is $V_\alpha(i) = \inf_\theta V_{\theta,\alpha}(i)$, the infimum over all policies for the infinite horizon;
--   3. a policy $\theta$ is optimal for the expected discounted cost criterion if $V_{\theta,\alpha}(i) = V_\alpha(i)$ for every $i \in S$.
--
--   All of these quantities take values in $[0, \infty]$ and may equal $+\infty$.
--
--   **Formalization Note** Values are in `ℝ≥0∞` and all sums over states and histories are `ℝ≥0∞` sums, so no summability conditions arise; the convention $0 \cdot \infty = 0$ applies. The discount factor is `α : ℝ≥0`. The infima range over the type of all general policies; an $n$-horizon policy is the restriction of such a policy to the times $0,\dots,n-1$, and every $n$-horizon policy arises this way.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 22–26, Section 2.3 (2.6)–(2.7) and Section 2.4 (2.9), (2.10), (2.13), (2.14), Definition 2.4.4; terminal cost zero as on pp. 61 and 66

import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace SennottDP.Discounted

variable {S : Type} [Countable S] {Act : Type}

open Classical in
/-- Sennott (1999), §2.3, pp. 22–23: the probability, under policy `θ` and initial state `i`,
of observing the history `h_n = (s 0, as 0, s 1, …, as (n-1), s n)`:
`P_θ(X_0 = s 0, A_0 = as 0, …, X_n = s n | X_0 = i)`. It is `1_{s 0 = i}` for `n = 0`, and
each further step multiplies by the probability `θ(a_n | h_n)` of the action and the transition
probability `P_{i_n i_{n+1}}(a_n)`. -/
noncomputable def histProb (M : MDC S Act) (θ : Policy M) (i : S) :
    (n : ℕ) → (Fin (n + 1) → S) → (Fin n → Act) → ℝ≥0∞
  | 0, s, _ => if s 0 = i then 1 else 0
  | n + 1, s, as =>
      histProb M θ i n (Fin.init s) (Fin.init as) *
        θ.dist n (Fin.init s) (Fin.init as) (as (Fin.last n)) *
        M.P (s (Fin.castSucc (Fin.last n))) (as (Fin.last n)) (s (Fin.last (n + 1)))

/-- Sennott (1999), (2.6), p. 23: the expected cost at time `t`,
`E_θ[C(X_t, A_t) | X_0 = i] = ∑_j ∑_{a ∈ A_j} C(j,a) P_θ(X_t = j, A_t = a | X_0 = i)`,
a value in `[0, ∞]`. -/
noncomputable def expCost (M : MDC S Act) (θ : Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act,
    histProb M θ i t s as *
      ∑ a ∈ M.A (s (Fin.last t)), θ.dist t s as a * (M.C (s (Fin.last t)) a : ℝ≥0∞)

/-- The conditional expectation `E_θ[W(X_n) | X_0 = i]` of a function `W : S → [0, ∞]` of the
state at time `n`, under policy `θ` and initial state `i`. -/
noncomputable def expState (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) (W : S → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑' s : Fin (n + 1) → S, ∑' as : Fin n → Act, histProb M θ i n s as * W (s (Fin.last n))

/-- Sennott (1999), (2.9), p. 25, with terminal cost `F = 0` (as on p. 61 and p. 66): the
`n`-horizon expected discounted cost `v_{θ,α,n}(i) = ∑_{t=0}^{n-1} α^t E_θ[C(X_t,A_t) | X_0 = i]`.
For `n = 0` it is `0`. -/
noncomputable def finiteHorizonCost (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (n : ℕ) (i : S) :
    ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, (α : ℝ≥0∞) ^ t * expCost M θ i t

/-- Sennott (1999), (2.13), p. 26: the infinite horizon expected discounted cost
`V_{θ,α}(i) = ∑_{t=0}^∞ α^t E_θ[C(X_t,A_t) | X_0 = i]`, a value in `[0, ∞]`. -/
noncomputable def discountedCost (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, (α : ℝ≥0∞) ^ t * expCost M θ i t

/-- Sennott (1999), (2.14), p. 26: the discounted value function
`V_α(i) = inf_θ V_{θ,α}(i)`, the infimum over all (general) policies for the infinite horizon. -/
noncomputable def valueFn (M : MDC S Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, discountedCost M θ α i

/-- Sennott (1999), (2.10), p. 25, with terminal cost `F = 0` (p. 66): the `n`-horizon expected
discounted value function `v_{α,n}(i) = inf_θ v_{θ,α,n}(i)`, the infimum over all policies. An
`n`-horizon policy is the restriction of a policy to the times `0, …, n-1`, and every
`n`-horizon policy arises this way, so the infimum is taken over `Policy M`. -/
noncomputable def finiteValueFn (M : MDC S Act) (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, finiteHorizonCost M θ α n i

/-- Sennott (1999), Definition 2.4.4, p. 26: a policy `θ` is optimal for the expected discounted
cost criterion if `V_{θ,α}(i) = V_α(i)` for every `i ∈ S`. -/
def IsDiscountOptimal (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) : Prop :=
  ∀ i, discountedCost M θ α i = valueFn M α i

end SennottDP.Discounted


