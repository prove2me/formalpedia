-- Prove2me | Definitions.Def_BertsekasDPModel
-- name    : BertsekasDPModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-10T22:01:11.715466+00:00
-- url     : https://prove2.me/theorems/4442209a-04f8-4386-b001-fbd461ca449e
-- title:
--   The basic stochastic control model, policy costs, and the DP recursion
-- statement:
--   This module fixes the **basic problem** of finite-horizon stochastic optimal control (Bertsekas, Vol. I, §1.2), together with the two cost functionals built on it.
--
--   A system evolves over a horizon of $N$ stages according to
--
--   $$x_{k+1} = f_k(x_k, u_k, w_k), \qquad k = 0, 1, \dots, N-1,$$
--
--   where $x_k$ is the state, $u_k$ the control and $w_k$ the disturbance. The control applied at stage $k$ in state $x$ is constrained to a finite nonempty set $U_k(x)$, and the disturbance takes values in a finite space $W$ with conditional distribution $p_k(\cdot \mid x, u)$: for every admissible $u \in U_k(x)$ the weights $p_k(w \mid x,u)$ are nonnegative and sum to $1$. Costs are additive: stage $k$ costs $g_k(x_k,u_k,w_k)$ and the terminal state costs $g_N(x_N)$.
--
--   **Expected cost of a policy.** A policy $\pi = \{\mu_0, \mu_1, \dots\}$ assigns a control $\mu_k(x)$ to each stage and state. Writing $J_{\pi,m}$ for its expected cost over the last $m$ stages, the recursion is $J_{\pi,0} = g_N$ and, at stage $k = N - m - 1$,
--
--   $$J_{\pi,m+1}(x) \;=\; \sum_{w \in W} p_k(w \mid x, u)\Bigl[g_k(x,u,w) + J_{\pi,m}\bigl(f_k(x,u,w)\bigr)\Bigr], \qquad u = \mu_k(x).$$
--
--   The total expected cost of $\pi$ from an initial state $x_0$ is $J_{\pi,N}(x_0)$.
--
--   **The dynamic programming recursion.** The value functions are given backward in time by $J_N = g_N$ and
--
--   $$J_k(x) \;=\; \min_{u \in U_k(x)} \; \sum_{w \in W} p_k(w \mid x,u)\Bigl[g_k(x,u,w) + J_{k+1}\bigl(f_k(x,u,w)\bigr)\Bigr].$$
--
--   This is the model on which the whole series rests: the optimality of the DP recursion (Prop. 1.3.1) is stated over it, and the approximate-DP performance bounds of Chapter 6 (one-step lookahead, limited lookahead, open-loop feedback control) reuse it unchanged.
--
--   **Formalization Note** The state and control spaces are arbitrary types; only the disturbance space carries a finiteness assumption, so every expectation is a finite sum and no measure theory is involved. The constraint sets are finite and nonempty, so each minimum is attained. Both recursions are indexed by the number $m$ of *remaining* stages, with the stage index recovered as $k = N - m - 1$ in truncated natural-number subtraction; only the values at $m \le N$ carry meaning. The probability axioms are imposed exactly where the book imposes them — at admissible controls $u \in U_k(x)$.
--
--   **Environment note** This is the Chapter 1 model bundle of Mission I of this series, re-published in the current default environment (Lean v4.33.1 / Mathlib 0df444a) because Mission I's copy lives in the earlier c5ea003 environment and imports resolve only within one environment. The code is identical.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 1.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 1.3

import Mathlib

/-- The basic finite-horizon stochastic optimal control model of Bertsekas,
"Dynamic Programming and Optimal Control", Vol. I, 3rd ed., Section 1.2,
with finite disturbance space and finite control-constraint sets.
`f` is the system equation, `g` the stage cost, `gN` the terminal cost,
`U k x` the control constraint set at stage `k` and state `x`, and
`p k x u w` the probability that the stage-`k` disturbance equals `w`
given state `x` and control `u` (a probability distribution for every
admissible control `u ∈ U k x`). -/
structure BertsekasDPModel (S C W : Type) [Fintype W] where
  N : ℕ
  f : ℕ → S → C → W → S
  g : ℕ → S → C → W → ℝ
  gN : S → ℝ
  U : ℕ → S → Finset C
  hU : ∀ k x, (U k x).Nonempty
  p : ℕ → S → C → W → ℝ
  hp_nonneg : ∀ k x, ∀ u ∈ U k x, ∀ w, 0 ≤ p k x u w
  hp_sum : ∀ k x, ∀ u ∈ U k x, ∑ w, p k x u w = 1

/-- Expected cost-to-go of a policy `π` in the basic problem, by backward
recursion on the number `m` of remaining stages: `BertsekasDPPolicyCost M π m x`
is the expected cost of the last `m` stages when the state at stage `M.N - m`
is `x` and controls are chosen by `π`.  The total expected cost of `π` from
initial state `x₀` is `BertsekasDPPolicyCost M π M.N x₀`. -/
def BertsekasDPPolicyCost {S C W : Type} [Fintype W] (M : BertsekasDPModel S C W)
    (π : ℕ → S → C) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      let u := π k x
      ∑ w, M.p k x u w * (M.g k x u w + BertsekasDPPolicyCost M π m (M.f k x u w))

/-- The dynamic programming (value iteration) algorithm of Prop. 1.3.1:
`BertsekasDPValue M m x` is `J_{N-m}(x)`, computed backward from the terminal
condition `J_N = g_N` by minimizing the expected current stage cost plus
cost-to-go over the finite control constraint set. -/
noncomputable def BertsekasDPValue {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      (M.U k x).inf' (M.hU k x) fun u =>
        ∑ w, M.p k x u w * (M.g k x u w + BertsekasDPValue M m (M.f k x u w))


