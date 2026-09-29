-- Prove2me | Definitions.Def_LimitedBFGS_SQN_quadratic
-- name    : LimitedBFGS_SQN_quadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:22:59.785984+00:00
-- url     : https://prove2.me/theorems/4808617a-b062-43a4-b0e6-32a210952cb5
-- title:
--   Gradient $Ax + b$ of the quadratic $\tfrac12 x^TAx + b^Tx$ and the exact line-search step
-- statement:
--   Let $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and consider the quadratic function
--
--   $$f(x) = \tfrac12 x^T A x + b^T x .$$
--
--   For symmetric $A$ its gradient is $g(x) = A x + b$; this module defines $g(x) = Ax + b$ directly. For a point $x$ and a direction $d$, the **exact line-search step** is
--
--   $$\alpha(x, d) = -\frac{g(x)^T d}{d^T A d}.$$
--
--   When $A$ is symmetric positive definite (so $f$ is strictly convex) and $d \neq 0$, $\alpha(x,d)$ is the unique minimizer of $\alpha \mapsto f(x + \alpha d)$; this is what the paper means by "exact line searches" on a quadratic. A point $x$ with $g(x) = 0$ is the unique minimizer of $f$.
--
--   **Formalization Note** The function $f$ itself is not defined: every statement of the mission is phrased through $g$. For $d = 0$ the formula is $0/0$, which Lean evaluates to $0$, so the iterate does not move; this only happens after an iteration has reached the minimizer.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 775, Property (b) (f(x) = ½xᵀAx + bᵀx); p. 777 ('exact line searches are performed')

import Mathlib

open Matrix

namespace LimitedBFGS.SQN

/-- The gradient `g(x) = A x + b` of the quadratic `f(x) = ½ xᵀAx + bᵀx`
(Nocedal 1980, p. 775, Property (b)). -/
def grad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  A *ᵥ x + b

/-- The exact line-search step along `d` from `x` for `f(x) = ½ xᵀAx + bᵀx`:
`α = −(g(x)ᵀd) / (dᵀAd)`. For `A` positive definite and `d ≠ 0` this is the unique minimizer
of `α ↦ f(x + α d)` (Nocedal 1980, p. 777, "exact line searches"). For `d = 0` Lean's
`0 / 0 = 0` gives `α = 0`, and the iterate does not move. -/
noncomputable def exactStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (x d : Fin n → ℝ) : ℝ :=
  -(grad A b x ⬝ᵥ d) / (d ⬝ᵥ (A *ᵥ d))

end LimitedBFGS.SQN


