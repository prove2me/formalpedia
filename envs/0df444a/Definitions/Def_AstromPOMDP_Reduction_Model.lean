-- Prove2me | Definitions.Def_AstromPOMDP_Reduction_Model
-- name    : AstromPOMDP_Reduction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:55:33.204316+00:00
-- url     : https://prove2.me/theorems/b7a83472-862e-44bb-bc50-b2803ecb1959
-- title:
--   §II, pp. 177–179 — controlled finite Markov chain with incomplete state information, control laws, joint law and expected cost (2.6), problem P.1
-- statement:
--   This module fixes Åström's model of a controlled Markov chain observed through noisy measurements (§II), and problem P.1.
--
--   1. **Model.** A finite set $S$ of states and a finite set $Y$ of outputs (measurement values); a compact nonempty set $U\subset\mathbb R^r$ of admissible controls; transition probabilities $p_{ij}(u,t)=P\{x_t=j\mid x_{t-1}=i\}$ (2.1), nonnegative with $\sum_j p_{ij}(u,t)=1$ for $u\in U$ and continuous in $u$ on $U$; measurement probabilities $q_{ij}=P\{y_t=j\mid x_t=i\}$ (2.2), nonnegative with $\sum_j q_{ij}=1$; an instantaneous cost $g(u,i,t)$, continuous in $u$ on $U$; a horizon $N$; and the law $p^1$ of the first state $x_1$.
--   2. **Control laws.** A control law (2.4) is a family $c(\eta_1,\dots,\eta_t,t)$ giving the control $u(t)$ at time $t$ as a function of the outputs observed so far, $\eta(t)=(\eta_1,\dots,\eta_t)$ (2.3). It is admissible if $c(\eta(t),t)\in U$ for $t=1,\dots,N$ and all $\eta(t)$.
--   3. **Joint law.** Under a law $c$ the probability that the states are $x_1,\dots,x_n$ and the outputs $\eta_1,\dots,\eta_n$ is
--   $$
--   p^1(x_1)\,q_{x_1\eta_1}\prod_{t=1}^{n-1}p_{x_tx_{t+1}}\big(c(\eta(t),t),\,t+1\big)\,q_{x_{t+1}\eta_{t+1}} .
--   $$
--   4. **Expected cost (2.6)** $EL=E\sum_{t=1}^N g\big(c(\eta(t),t),x_t,t\big)$, the expectation under this joint law with $n=N$. Problem **P.1** asks for an admissible law whose expected cost is no larger than that of any admissible law.
--   5. **Output probabilities and conditional state distributions.** $P(\eta_1,\dots,\eta_t)$ is the joint law summed over the states, and $w_i(t)=P\{x_t=i\mid y_1=\eta_1,\dots,y_t=\eta_t\}$ (3.6) is the joint law summed over the state paths with $x_t=i$, divided by $P(\eta(t))$.
--
--   These are the objects every result of the paper is about. The cost is defined from the joint law of states and outputs, not through the conditional distributions $w(t)$, so the results that bring in $w(t)$ have content.
--
--   **Formalization Note** The paper's datum is the law $p^0$ of $x_0$, but no control $u(0)$ exists and the cost starts at $t=1$; the law $p^1$ of $x_1$ is taken as the datum (equivalently, $p^0$ followed by an uncontrolled first transition). The transition from $x_t$ to $x_{t+1}$ uses $u(t)$ and, by (2.1), the matrix $P(u(t),t+1)$. Index $i$ of `Fin n` is time $t=i+1$. The control dimension is called $r$ because the paper uses $k$ also for time. $w(t)$ is the conditional probability only when $P(\eta(t))\neq 0$ (Lean's division by zero returns $0$).
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, pp. 177–179, §II, (2.1)–(2.6), problem P.1; p. 180, (3.6)

import Mathlib

namespace AstromPOMDP.Reduction

/-- Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, §II, pp. 177–178:
the controlled finite Markov chain `{x_t}` observed through the outputs `y_t`.

* `St` is the finite state space `{1, …, n}`, `Obs` the finite output space `{1, …, m}`.
* Controls are vectors `u = (u₁, …, u_r) ∈ ℝ^r`; `U` is the compact set of admissible controls
  at fixed times (nonempty, as the paper tacitly assumes).
* `P u t i j = p_ij(u, t) = P{x_t = j | x_{t−1} = i}` (2.1): nonnegative, rows summing to one,
  continuous in `u` on `U`.
* `q i j = q_ij = P{y_t = j | x_t = i}` (2.2): nonnegative, rows summing to one.
* `g u i t = g(u, x, t)` is the instantaneous cost, continuous in `u` on `U`.
* `N` is the horizon (times `t = 1, …, N`).
* `p₁` is the law of the first state `x₁`.

**Formalization Note.** The paper's datum is the law `p⁰` of `x₀`, but no control `u(0)` exists
and the cost and value (3.29) start at `t = 1`; the law of `x₁` is taken as the datum (equivalently,
`p⁰` followed by an uncontrolled first transition). The control dimension is called `r` here
because the paper uses `k` both for it and for the time index of `V_k`. -/
structure Model (St Obs : Type*) [Fintype St] [Fintype Obs] (r : ℕ) where
  /-- The set `U` of admissible controls at fixed times. -/
  U : Set (Fin r → ℝ)
  /-- `P u t i j = p_ij(u, t)`, (2.1). -/
  P : (Fin r → ℝ) → ℕ → St → St → ℝ
  /-- `q i j = q_ij`, (2.2). -/
  q : St → Obs → ℝ
  /-- `g u i t = g(u, i, t)`, the instantaneous cost. -/
  g : (Fin r → ℝ) → St → ℕ → ℝ
  /-- The horizon `N`. -/
  N : ℕ
  /-- The law of `x₁`. -/
  p₁ : St → ℝ
  U_compact : IsCompact U
  U_nonempty : U.Nonempty
  P_nonneg : ∀ u ∈ U, ∀ t i j, 0 ≤ P u t i j
  P_sum : ∀ u ∈ U, ∀ t i, ∑ j, P u t i j = 1
  P_cont : ∀ t i j, ContinuousOn (fun u => P u t i j) U
  q_nonneg : ∀ i j, 0 ≤ q i j
  q_sum : ∀ i, ∑ j, q i j = 1
  g_cont : ∀ i t, ContinuousOn (fun u => g u i t) U
  p₁_nonneg : ∀ i, 0 ≤ p₁ i
  p₁_sum : ∑ i, p₁ i = 1

/-- A control law (strategy) `C = {c(η₁, …, η_t, t)}` (2.4): `c t η` is the control `u(t)` used at
time `t` after the outputs `η(t) = (η₁, …, η_t)` (2.3) have been observed. -/
abbrev ControlLaw (Obs : Type*) (r : ℕ) : Type _ := (t : ℕ) → (Fin t → Obs) → (Fin r → ℝ)

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}

/-- p. 178: the control law `C` is admissible if `c(η₁, …, η_t, t) ∈ U` for all `t = 1, …, N`
and all possible `η_t`. -/
def Admissible (M : Model St Obs r) (c : ControlLaw Obs r) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ M.N → ∀ η : Fin t → Obs, c t η ∈ M.U

/-- The joint probability, under the control law `c`, that the states at times `1, …, n` are
`x 0, …, x (n−1)` and the outputs at times `1, …, n` are `y 0, …, y (n−1)`:
`p₁(x₁) q(x₁, y₁) ∏_{t=1}^{n−1} p_{x_t x_{t+1}}(c(η(t), t), t + 1) q(x_{t+1}, y_{t+1})`.

**Formalization Note.** Index `i` of `Fin n` is the paper's time `t = i + 1`. The transition from
`x_t` to `x_{t+1}` uses the control `u(t) = c(η(t), t)` chosen after `y_t` is observed and, by (2.1),
the matrix `P(u(t), t + 1)`. The outputs are conditionally independent given the states. -/
noncomputable def pathProb (M : Model St Obs r) (c : ControlLaw Obs r) :
    (n : ℕ) → (Fin n → St) → (Fin n → Obs) → ℝ
  | 0, _, _ => 1
  | 1, x, y => M.p₁ (x 0) * M.q (x 0) (y 0)
  | n + 2, x, y =>
      pathProb M c (n + 1) (Fin.init x) (Fin.init y) *
        M.P (c (n + 1) (Fin.init y)) (n + 2) (x (Fin.last n).castSucc) (x (Fin.last (n + 1))) *
        M.q (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))

/-- (2.6): the expected total cost `E L = E Σ_{t=1}^N g(c(η₁, …, η_t, t), x_t, t)` of the control
law `c`, the expectation being taken under the joint law `pathProb` of `(x₁, …, x_N, y₁, …, y_N)`.
The cost is defined from the joint law of states and outputs, not through the conditional
distributions `w(t)`. -/
noncomputable def expectedCost (M : Model St Obs r) (c : ControlLaw Obs r) : ℝ :=
  ∑ x : Fin M.N → St, ∑ y : Fin M.N → Obs,
    pathProb M c M.N x y *
      ∑ i : Fin M.N, M.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y)) (x i) (i.val + 1)

/-- Problem P.1 (p. 179): `c` solves P.1 if it is admissible and its expected total cost (2.6) is
no larger than that of every admissible control law. -/
def IsOptimalP1 (M : Model St Obs r) (c : ControlLaw Obs r) : Prop :=
  Admissible M c ∧ ∀ c' : ControlLaw Obs r, Admissible M c' → expectedCost M c ≤ expectedCost M c'

/-- `P(y₁ = η₁, …, y_t = η_t)` under the control law `c`: the marginal of the joint law of the
first `t` states and outputs. -/
noncomputable def obsProb (M : Model St Obs r) (c : ControlLaw Obs r) (t : ℕ) (η : Fin t → Obs) :
    ℝ :=
  ∑ x : Fin t → St, pathProb M c t x η

/-- (3.6): the conditional state distribution
`w_i(n + 1) = P{x_{n+1} = i | y₁ = η₁, …, y_{n+1} = η_{n+1}}` under the control law `c`, computed
from the joint law as a ratio of path sums. It is the paper's conditional probability only when
`obsProb M c (n + 1) η ≠ 0`; otherwise Lean's division returns `0`. -/
noncomputable def condState (M : Model St Obs r) (c : ControlLaw Obs r) (n : ℕ)
    (η : Fin (n + 1) → Obs) (i : St) : ℝ :=
  (∑ x : Fin (n + 1) → St, if x (Fin.last n) = i then pathProb M c (n + 1) x η else 0) /
    obsProb M c (n + 1) η

end AstromPOMDP.Reduction


