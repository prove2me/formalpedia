-- Prove2me | Definitions.Def_AndersonAccel_Safe_Basic
-- name    : AndersonAccel_Safe_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:04:14.406048+00:00
-- url     : https://prove2.me/theorems/1860a3b4-90ac-4282-8c64-868c763808b7
-- title:
--   Residual $g(x)=x-f(x)$, KM operator $f_\alpha$, and Powell's weight $\phi_{\bar\theta}$ of Eq. (3.4)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be a map. This file fixes three elementary objects used throughout the analysis of stabilized type-I Anderson acceleration.
--
--   1. **Residual.** $g(x)=x-f(x)$. A point $x$ solves the fixed-point problem $x=f(x)$ exactly when $g(x)=0$.
--   2. **Averaged (Krasnosel'skiĭ–Mann) operator.** For $\alpha\in\mathbb R$,
--   $$f_\alpha(x)=(1-\alpha)x+\alpha f(x).$$
--   3. **Powell's weight.** For a parameter $\bar\theta$ and $\eta\in\mathbb R$,
--   $$\phi_{\bar\theta}(\eta)=\begin{cases}1 & \text{if } |\eta|\ge\bar\theta,\\[2pt] \dfrac{1-\operatorname{sign}(\eta)\,\bar\theta}{1-\eta} & \text{if } |\eta|<\bar\theta,\end{cases}$$
--   with the convention $\operatorname{sign}(0)=1$.
--
--   The weight $\phi_{\bar\theta}$ is the regularization that keeps the rank-one updates of the algorithm nonsingular; $f_\alpha$ is the fallback step used by the safeguard.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so norms are Euclidean. The sign with $\operatorname{sign}(0)=1$ is the separate function `signOne` ($1$ if $\eta\ge0$, $-1$ otherwise), because Mathlib's `Real.sign 0 = 0`. When $|\eta|<\bar\theta<1$ the denominator $1-\eta$ is positive, so no division by zero occurs in the paper's range.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3173 (residual g), p. 3176, Eq. (3.4) (φ_θ̄, sign(0) = 1), p. 3178, Section 3.3 (f_α)

import Mathlib

namespace AndersonAccel.Safe

/-- The residual `g(x) = x - f(x)` of a map `f : ℝⁿ → ℝⁿ` (Zhang–O'Donoghue–Boyd 2020, p. 3173). -/
noncomputable def residual {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - f x

/-- The α-averaged (Krasnosel'skiĭ–Mann) operator `f_α(x) = (1 - α) x + α f(x)` (p. 3178). -/
noncomputable def fAlpha {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 - α) • x + α • f x

/-- The sign function with the paper's convention `sign(0) = 1` (p. 3176). -/
noncomputable def signOne (η : ℝ) : ℝ := if 0 ≤ η then 1 else -1

/-- Powell's weight, Eq. (3.4) (p. 3176):
`φ_θ̄(η) = 1` if `|η| ≥ θ̄`, and `(1 - sign(η) θ̄) / (1 - η)` if `|η| < θ̄`, with `sign(0) = 1`. -/
noncomputable def phiTheta (θbar η : ℝ) : ℝ :=
  if θbar ≤ |η| then 1 else (1 - signOne η * θbar) / (1 - η)

end AndersonAccel.Safe


