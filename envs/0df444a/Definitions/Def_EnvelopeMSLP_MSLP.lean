-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP
-- name    : EnvelopeMSLP_MSLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:05.5262+00:00
-- url     : https://prove2.me/theorems/d0d32052-159c-4b3f-bd8d-0d7de798a024
-- title:
--   Finitely supported multi-stage linear stochastic program
-- statement:
--   The data of the program (7): a horizon $T$, decision dimensions, constraint counts and noise dimensions per stage, matrices and vectors $W_t(\theta,\alpha)$, $T_t(\theta,\alpha)$, $c_t(\theta,\alpha)$, $h_t(\theta,\alpha)$ of fitting dimension for a parameter $\theta$ and a noise value $\alpha$, a given $x_0$, and a discrete process $\xi=(\xi_1,\dots,\xi_T)$ on a finite scenario set $\Omega$ with probabilities $p(\omega)>0$ summing to $1$.
--
--   **Formalization Note** Stage $t$ of type `Fin T` is the paper's stage $t+1$. The finite $\Omega$ with positive probabilities is the support of the law of $\xi$; a general $(\Omega,\mathcal F,\mathbb P)$ pushes forward onto it, and two scenarios may carry the same noise. `Tmat` is the technology matrix, because `T` is the horizon. The data are functions on all of $\mathbb R$, and only their values on $\Theta$ enter a statement.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), pp.11–12; Theorem 3, p.13

import Mathlib

namespace EnvelopeMSLP

/-- **A finitely supported multi-stage linear stochastic program with parameter `θ`.**
Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), pp.11–12, Theorem 3, p.13.

There are `T` stages. Stage `t : Fin T` is the paper's stage `t + 1`, with `n t.succ` decisions,
`m t` constraints and noise `ξ_t ∈ ℝ^{M t}`; `n 0` is the dimension of the given `x₀`. For a parameter
`θ` and a noise value `α`, the fields `W t θ α`, `Tmat t θ α`, `c t θ α`, `h t θ α` are the paper's
`W_t(θ, α)`, `T_t(θ, α)`, `c_t(θ, α)`, `h_t(θ, α)`. The noise lives on a finite scenario type `Ω` with
probabilities `p`.

**Formalization Note.** `T` is the horizon and `Tmat` the technology matrix. The finite type `Ω`
with `p ω > 0` is the support of the law of the discrete process `ξ` (p.12: "the image measure of
`ξ` is made up of finitely many atoms"); a general `(Ω, F, P)` pushes forward onto it, and two
scenarios may carry the same noise. Every entry is a function on all of `ℝ`; only its values on
`Θ` enter a statement. `Ω` is nonempty because the probabilities sum to `1`. -/
structure MSLP (T : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- decision dimensions: `n 0` is that of `x₀`, `n t.succ` that of stage `t` -/
  n : Fin (T + 1) → ℕ
  /-- number of constraints of stage `t` -/
  m : Fin T → ℕ
  /-- noise dimension of stage `t` -/
  M : Fin T → ℕ
  /-- recourse matrix `W_t(θ, α)` -/
  W : (t : Fin T) → ℝ → (Fin (M t) → ℝ) → Matrix (Fin (m t)) (Fin (n t.succ)) ℝ
  /-- technology matrix `T_t(θ, α)` -/
  Tmat : (t : Fin T) → ℝ → (Fin (M t) → ℝ) → Matrix (Fin (m t)) (Fin (n t.castSucc)) ℝ
  /-- objective `c_t(θ, α)` -/
  c : (t : Fin T) → ℝ → (Fin (M t) → ℝ) → Fin (n t.succ) → ℝ
  /-- right-hand side `h_t(θ, α)` -/
  h : (t : Fin T) → ℝ → (Fin (M t) → ℝ) → Fin (m t) → ℝ
  /-- the given initial decision `x₀` -/
  x0 : Fin (n 0) → ℝ
  /-- scenario probabilities -/
  p : Ω → ℝ
  hp_pos : ∀ ω, 0 < p ω
  hp_sum : ∑ ω, p ω = 1
  /-- the noise `ξ_t(ω)` -/
  ξ : (t : Fin T) → Ω → Fin (M t) → ℝ

end EnvelopeMSLP


