-- Prove2me | Definitions.Def_LimitedBFGS_SQN_pcgIter
-- name    : LimitedBFGS_SQN_pcgIter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:24:16.159495+00:00
-- url     : https://prove2.me/theorems/3bbf4253-3a33-4b98-a53c-fb0295d422a8
-- title:
--   Preconditioned conjugate gradients with fixed preconditioner $H_0$ and exact line searches
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ on $\mathbb{R}^n$ with gradient $g(x) = Ax + b$, let $H_0$ be a fixed preconditioner and $x_0$ a starting point. The **PCG with fixed preconditioner $H_0$** generates, for $i = 0, 1, 2, \dots$,
--
--   $$d_0 = -H_0 g_0, \qquad x_{i+1} = x_i + \alpha_i d_i, \qquad d_{i+1} = -H_0 g_{i+1} + \beta_{i+1} d_i, \qquad \beta_{i+1} = \frac{y_i^T H_0 g_{i+1}}{y_i^T d_i},$$
--
--   where $g_i = g(x_i)$, $y_i = g_{i+1} - g_i$, and $\alpha_i$ is the exact line-search step along $d_i$. This is Nazareth's form of preconditioned conjugate gradients, iteration (13) of the paper with the fixed matrix $H_0$ in place of every $H_{i-1}$, as in (14).
--
--   It is the reference method to which the paper compares its limited-storage methods: on a strictly convex quadratic with exact line searches, the SQN iteration produces exactly the same iterates.
--
--   **Formalization Note** The denominator of $\beta$ is $y_{i}^T d_{i}$ (in the paper's indexing $y_{i-1}^T d_{i-1}$), as in (12) and on p. 778; the printed (13) has $y_{i-1}^T d_i$, which is zero on a quadratic with exact line searches and is a misprint. The numerator carries the preconditioner, $y^T H_0 g$, as in (13) and p. 778 ((12) omits it). Indices are 0-based. After $g_k = 0$, $\beta = 0$ (Lean's $0/0 = 0$ when also $y^T d = 0$), all later directions are $0$, and the iterate remains at the minimizer.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 776, eq. (12); p. 777, eqs. (13)–(14) ('PCG with fixed preconditioner H_0'); p. 778 (β_{m+2} with denominator y_{m+1}ᵀd_{m+1})

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix

namespace LimitedBFGS.SQN

/-- State of the preconditioned conjugate gradient iteration: iterate `x` and direction `d`. -/
structure PCGState (n : ℕ) where
  /-- the current iterate `x_k` -/
  x : Fin n → ℝ
  /-- the current search direction `d_k` -/
  d : Fin n → ℝ

/-- The PCG with fixed preconditioner `H₀` (Nocedal 1980, p. 777: iteration (13) with `H₀` in
place of every `H_{i−1}`, cf. (14)) on `f(x) = ½ xᵀAx + bᵀx` with exact line searches, started at
`x₀` (0-based): `d₀ = −H₀ g₀`, `x_{i+1} = x_i + α_i d_i`,
`d_{i+1} = −H₀ g_{i+1} + β_{i+1} d_i` with `β_{i+1} = y_iᵀ H₀ g_{i+1} / y_iᵀ d_i` and
`y_i = g_{i+1} − g_i`. (The denominator `y_iᵀ d_i` corrects the printed `y_{i−1}ᵀ d_i` of (13),
following (12) and p. 778.) After `g_k = 0`, `β = 0`, all later directions are `0`, and the
iterate stays put. -/
noncomputable def pcgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) : ℕ → PCGState n
  | 0 => ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩
  | k + 1 =>
    let st := pcgIter A b H₀ x₀ k
    let x' := st.x + exactStep A b st.x st.d • st.d
    let y := grad A b x' - grad A b st.x
    let β := (y ⬝ᵥ (H₀ *ᵥ grad A b x')) / (y ⬝ᵥ st.d)
    ⟨x', -(H₀ *ᵥ grad A b x') + β • st.d⟩

end LimitedBFGS.SQN


