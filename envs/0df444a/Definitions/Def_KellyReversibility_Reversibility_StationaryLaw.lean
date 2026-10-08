-- Prove2me | Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
-- name    : KellyReversibility_Reversibility_StationaryLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:04:22.724531+00:00
-- url     : https://prove2.me/theorems/4d0b686d-a2a5-4d93-9a24-05994f385c5f
-- title:
--   Finite-dimensional distributions of a stationary Markov process, reversibility, and Kolmogorov's cycle condition
-- statement:
--   Let $\mathcal S$ be a state space and let $\mathcal T$ be the time set ($\mathbb Z$ or $\mathbb R$). A stationary Markov process $X(t)$, $t\in\mathcal T$, is described by its **equilibrium distribution** $\pi=(\pi(j))_{j\in\mathcal S}$ and by the matrices $T(s)=(T(s)(j,k))_{j,k\in\mathcal S}$ of transition probabilities over a time lag $s\ge 0$, $T(s)(j,k)=P(X(u+s)=k\mid X(u)=j)$.
--
--   1. **Finite-dimensional distributions.** For time points $t_0,\dots,t_n\in\mathcal T$ (in any order, repetitions allowed) and states $j_0,\dots,j_n$, sort the times increasingly by a permutation $\sigma$, $t_{\sigma(0)}\le t_{\sigma(1)}\le\dots\le t_{\sigma(n)}$, and set
--   $$P\bigl(X(t_0)=j_0,\dots,X(t_n)=j_n\bigr)=\pi(j_{\sigma(0)})\prod_{r=0}^{n-1}T\bigl(t_{\sigma(r+1)}-t_{\sigma(r)}\bigr)\bigl(j_{\sigma(r)},j_{\sigma(r+1)}\bigr).$$
--   2. **Reversibility** (Kelly, p. 5). The process is *reversible* if $(X(t_1),\dots,X(t_n))$ has the same distribution as $(X(\tau-t_1),\dots,X(\tau-t_n))$ for all $t_1,\dots,t_n,\tau\in\mathcal T$, that is, if the probabilities in item 1 are unchanged when every $t_r$ is replaced by $\tau-t_r$.
--   3. **Kolmogorov's cycle condition** (equations (1.21)/(1.22)). A rate or transition function $q$ satisfies it if, for every finite sequence of states $j_1,\dots,j_n$,
--   $$q(j_1,j_2)q(j_2,j_3)\cdots q(j_{n-1},j_n)q(j_n,j_1)=q(j_1,j_n)q(j_n,j_{n-1})\cdots q(j_3,j_2)q(j_2,j_1).$$
--
--   These three notions are shared by the discrete-time and continuous-time halves of Chapter 1: reversibility is the distributional property, and the cycle condition is the algebraic test for it.
--
--   **Formalization Note** The law is defined for any time type with a linear order and a subtraction, and $T$ is a function of the lag. Sorting uses Mathlib's `Tuple.sort`; with tied times the lag is $0$ and $T(0)$ is the identity in both applications in this mission. Tuples have $n+1\ge 1$ entries. The cycle condition quantifies over all lengths $n\ge 0$ (the cases $n\le 2$ hold trivially) and all sequences, with repetitions; `finRotate` closes the cycle.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 5, Definition (reversible); p. 21, Eq. (1.21); p. 23, Eq. (1.22)

import Mathlib

namespace KellyReversibility.Reversibility

/-- **Finite-dimensional distributions of a stationary Markov process.**
Let `T s` be the matrix of transition probabilities over a time lag `s ≥ 0` and `π` the
equilibrium distribution.  For time points `t 0, …, t n` (in any order, repetitions allowed)
and states `j 0, …, j n`, `fdd T π t j` is
`P(X(t 0) = j 0, …, X(t n) = j n)`: with the time points sorted increasingly by the
permutation `σ = Tuple.sort t`, it is
`π(j_{σ 0}) * ∏_r T(t_{σ(r+1)} - t_{σ r})(j_{σ r}, j_{σ(r+1)})`. -/
noncomputable def fdd {α S : Type*} [LinearOrder α] [Sub α] (T : α → Matrix S S ℝ)
    (π : S → ℝ) {n : ℕ} (t : Fin (n + 1) → α) (j : Fin (n + 1) → S) : ℝ :=
  π (j (Tuple.sort t 0)) *
    ∏ r : Fin n, T (t (Tuple.sort t r.succ) - t (Tuple.sort t r.castSucc))
      (j (Tuple.sort t r.castSucc)) (j (Tuple.sort t r.succ))

/-- **Reversibility** (Kelly, p. 5): `(X(t₁), …, X(tₙ))` has the same distribution as
`(X(τ - t₁), …, X(τ - tₙ))` for all `t₁, …, tₙ, τ`, the finite-dimensional distributions
being those of `fdd T π`. -/
def IsReversibleLaw {α S : Type*} [LinearOrder α] [Sub α] (T : α → Matrix S S ℝ)
    (π : S → ℝ) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → α) (j : Fin (n + 1) → S) (τ : α),
    fdd T π t j = fdd T π (fun r => τ - t r) j

/-- **Kolmogorov's cycle condition** (1.21)/(1.22): for every finite sequence of states
`j 0, …, j (n-1)` (repetitions allowed), the product of `q` around the closed cycle
`j 0 → j 1 → ⋯ → j (n-1) → j 0` equals the product around the reversed cycle.
`finRotate n` sends `r` to `r + 1` and the last index to `0`. -/
def KolmogorovCycle {S : Type*} (q : S → S → ℝ) : Prop :=
  ∀ (n : ℕ) (j : Fin n → S),
    ∏ r, q (j r) (j (finRotate n r)) = ∏ r, q (j (finRotate n r)) (j r)

end KellyReversibility.Reversibility


