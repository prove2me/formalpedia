-- Prove2me | Definitions.Def_SuttonBartoRL_Traces_LambdaReturn
-- name    : SuttonBartoRL_Traces_LambdaReturn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:17:34.453229+00:00
-- url     : https://prove2.me/theorems/4d418da1-c83e-4b83-96e4-e8ae3e566e22
-- title:
--   Episodes, $n$-step returns, the $\lambda$-return, TD errors and the accumulating trace for a fixed weight vector
-- statement:
--   An **episode** $S_0, R_1, S_1, R_2, \dots, R_T, S_T$ has a termination time $T \in \mathbb N$, nonterminal states $S_t$ ($t < T$) in a state set $\mathcal S$, and rewards $R_k \in \mathbb R$ ($1 \le k \le T$). Let $\hat v : \mathcal S \times \mathbb R^d \to \mathbb R$ be a parameterized value function and fix **one weight vector** $w \in \mathbb R^d$ for the whole episode. Write $\hat v(S_t, w)$ for the value at time $t$, with the convention $\hat v(\text{terminal}, \cdot) = 0$, so the value at every time $t \ge T$ is $0$. Let $\gamma$ be a discount rate and $\lambda$ a trace-decay parameter.
--
--   1. The **return** is $G_t = \sum_{k=t}^{T-1} \gamma^{k-t} R_{k+1}$ ($G_t = 0$ for $t \ge T$).
--   2. The **$n$-step return** (12.1) is
--   $$
--   G_{t:t+n} = R_{t+1} + \gamma R_{t+2} + \cdots + \gamma^{n-1} R_{t+n} + \gamma^n \hat v(S_{t+n}, w) \quad (t + n \le T),
--   $$
--   and $G_{t:t+n} = G_t$ when $t + n \ge T$. The two formulas agree at $t + n = T$.
--   3. The **$\lambda$-return** (12.2) is
--   $$
--   G^\lambda_t = (1 - \lambda) \sum_{n=1}^{\infty} \lambda^{n-1} G_{t:t+n}.
--   $$
--   4. The **TD error** (12.6) is $\delta_t = R_{t+1} + \gamma \hat v(S_{t+1}, w) - \hat v(S_t, w)$.
--   5. The **accumulating eligibility trace** (12.5) is $z_{-1} = 0$, $z_t = \gamma\lambda z_{t-1} + \nabla \hat v(S_t, w)$, so $z_0 = \nabla\hat v(S_0, w)$.
--
--   These are the objects of the off-line $\lambda$-return algorithm (12.4) and of TD($\lambda$) (12.5)–(12.7), evaluated at a weight vector that is not changed during the episode, as Exercises 12.3 and 12.4 assume.
--
--   **Formalization Note** Weights live in `EuclideanSpace ℝ (Fin d)` and $\nabla\hat v(s, w)$ is Mathlib's `gradient (vhat s) w`. The weights of (12.1), (12.4)–(12.6) are all the same fixed $w$; the time-varying weights $w_t$ of the running algorithms are not modelled. The series in (12.2) is a `tsum` and is written with $n$ shifted down by one ($\sum_{n \ge 0} \lambda^n G_{t:t+n+1}$). It is meaningful for $\lambda \in [0, 1)$, the range the book gives with (12.2). The states $S_t$ for $t \ge T$ and the rewards $R_k$ for $k > T$ are never used.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (12.1), p. 288; Eq. (12.2) and the text after it, p. 289; Eqs. (12.5)–(12.6) and the box Semi-gradient TD(λ), pp. 292–293

import Mathlib

namespace SuttonBartoRL.Traces

/-- An episode `S_0, R_1, S_1, R_2, …, R_T, S_T` (Sutton & Barto, Ch. 12): `T` is the time of
termination, `S t` is the nonterminal state `S_t` for `t < T` (its values for `t ≥ T` are never
used: `S_T` is the terminal state), and `R k` is the reward `R_k` for `1 ≤ k ≤ T`. -/
structure Episode (St : Type) where
  T : ℕ
  S : ℕ → St
  R : ℕ → ℝ

variable {St : Type} {d : ℕ}

/-- The approximate value `v̂(S_t, w)` of the state at time `t` for a **fixed** weight vector `w`,
with the convention `v̂(terminal, ·) = 0` (box "Semi-gradient TD(λ)", p. 293): it is `0` for `t ≥ T`. -/
noncomputable def value (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (e : Episode St) (t : ℕ) : ℝ :=
  if t < e.T then vhat (e.S t) w else 0

/-- The (discounted) return `G_t = R_{t+1} + γ R_{t+2} + ⋯ + γ^{T−t−1} R_T`; `G_t = 0` for `t ≥ T`. -/
def ret (γ : ℝ) (e : Episode St) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico t e.T, γ ^ (k - t) * e.R (k + 1)

/-- The `n`-step return (12.1) for a fixed weight vector `w`:
`G_{t:t+n} = R_{t+1} + γ R_{t+2} + ⋯ + γ^{n−1} R_{t+n} + γ^n v̂(S_{t+n}, w)` for `t + n ≤ T`, and
`G_{t:t+n} = G_t` for `t + n ≥ T` (p. 289; the two agree at `t + n = T` since `v̂(S_T, ·) = 0`). -/
noncomputable def nstepReturn (γ : ℝ) (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) (t n : ℕ) : ℝ :=
  if t + n ≤ e.T then
    (∑ i ∈ Finset.range n, γ ^ i * e.R (t + i + 1)) + γ ^ n * value vhat w e (t + n)
  else ret γ e t

/-- The λ-return (12.2) for a fixed weight vector `w`:
`G^λ_t ≐ (1 − λ) Σ_{n=1}^∞ λ^{n−1} G_{t:t+n}`, written with `n` shifted down by one. -/
noncomputable def lambdaReturn (γ lam : ℝ) (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) (t : ℕ) : ℝ :=
  (1 - lam) * ∑' n : ℕ, lam ^ n * nstepReturn γ vhat w e t (n + 1)

/-- The TD error (12.6) for a fixed weight vector `w`:
`δ_t ≐ R_{t+1} + γ v̂(S_{t+1}, w) − v̂(S_t, w)`. -/
noncomputable def tdError (γ : ℝ) (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) (t : ℕ) : ℝ :=
  e.R (t + 1) + γ * value vhat w e (t + 1) - value vhat w e t

/-- The accumulating eligibility trace (12.5) for a fixed weight vector `w`:
`z_{−1} ≐ 0`, `z_t ≐ γλ z_{t−1} + ∇v̂(S_t, w)`, so `z_0 = ∇v̂(S_0, w)`. -/
noncomputable def accTrace (γ lam : ℝ) (vhat : St → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (e : Episode St) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => gradient (vhat (e.S 0)) w
  | t + 1 => (γ * lam) • accTrace γ lam vhat w e t + gradient (vhat (e.S (t + 1))) w

end SuttonBartoRL.Traces


