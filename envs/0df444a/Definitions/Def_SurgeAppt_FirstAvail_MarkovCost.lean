-- Prove2me | Definitions.Def_SurgeAppt_FirstAvail_MarkovCost
-- name    : SurgeAppt_FirstAvail_MarkovCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:26.472909+00:00
-- url     : https://prove2.me/theorems/da233f50-8926-43e9-a6f1-d1fe92270d1b
-- title:
--   Law of a time-inhomogeneous finite Markov chain and its expected total discounted cost $\sum_t \beta^t\,\mathbb E[c_t(X_t)]$
-- statement:
--   This file defines two general objects that the appointment-scheduling model is built on: the law of a Markov chain on a finite state set, and the expected total discounted cost along it.
--
--   Let $X$ be a finite set of states, and for every time $t \in \{0,1,2,\dots\}$ let $k_t(x,x')$ be the probability of moving from $x$ to $x'$ at time $t$ (the kernel may change with $t$). Started at $x_0$, the law of the state at time $t$ is
--
--   $$
--   \mu_0(x) = \mathbf 1\{x = x_0\},\qquad \mu_{t+1}(x') = \sum_{x\in X} \mu_t(x)\,k_t(x,x').
--   $$
--
--   Given a stage cost $c_t(x)$ and a discount factor $\beta$, the expected total discounted cost from $x_0$ is the series
--
--   $$
--   \sum_{t=0}^{\infty} \beta^t \sum_{x\in X} \mu_t(x)\, c_t(x) \;=\; \sum_{t=0}^{\infty}\beta^t\,\mathbb E\big[c_t(X_t)\big].
--   $$
--
--   These are the objects behind the value of a (possibly non-stationary) Markov policy in any finite discounted dynamic program: the policy fixes the kernels $k_t$ and the stage costs $c_t$.
--
--   **Formalization Note** The series is a Lean `tsum`, which equals the limit of its partial sums whenever the series converges and is $0$ otherwise; in the appointment model the stage costs are bounded and nonnegative, so the series converges. The chain only moves within $X$: mass sent to states outside $X$ is not propagated.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), pp. 9–10, (9) (the expectation of the discounted cost series)

import Mathlib

namespace SurgeAppt.FirstAvail

/-- The law at time `t` of a (possibly time-inhomogeneous) Markov chain on the finite state set `X`,
started at `x₀`, whose one-step transition probability from `x` to `x'` at time `t` is `k t x x'`:
`chainLaw X k x₀ 0` is the point mass at `x₀`, and
`chainLaw X k x₀ (t+1) x' = ∑_{x ∈ X} chainLaw X k x₀ t x · k t x x'`. -/
def chainLaw {σ : Type*} [DecidableEq σ] (X : Finset σ) (k : ℕ → σ → σ → ℝ) (x₀ : σ) :
    ℕ → σ → ℝ
  | 0 => fun x => if x = x₀ then 1 else 0
  | t + 1 => fun x' => ∑ x ∈ X, chainLaw X k x₀ t x * k t x x'

/-- The expected total discounted cost `∑_{t ≥ 0} β^t E[c_t(X_t)]` of the chain `chainLaw X k x₀`,
with stage cost `c t x` at time `t` in state `x`, written as the series of the discounted expected
stage costs (a `tsum`; it is the limit of the partial sums whenever the series converges). -/
noncomputable def discountedCost {σ : Type*} [DecidableEq σ] (X : Finset σ) (k : ℕ → σ → σ → ℝ)
    (c : ℕ → σ → ℝ) (β : ℝ) (x₀ : σ) : ℝ :=
  ∑' t : ℕ, β ^ t * ∑ x ∈ X, chainLaw X k x₀ t x * c t x

end SurgeAppt.FirstAvail


