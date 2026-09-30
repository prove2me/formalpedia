-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds
-- name    : SolodovSvaiterVI_Alg21_ArmijoHolds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:05:56.453267+00:00
-- url     : https://prove2.me/theorems/e84f17ce-3981-40d9-9266-947c4d2fab95
-- title:
--   Armijo-type linesearch condition (2.1)
-- statement:
--   Let $C \subseteq \mathbb{R}^n$, $F : \mathbb{R}^n \to \mathbb{R}^n$, parameters $\gamma, \sigma \in \mathbb{R}$, a point $x \in \mathbb{R}^n$ and a nonnegative integer $k$, and let $r$ be the projected residual of $\mathrm{VI}(F, C)$. The integer $k$ **satisfies the linesearch condition (2.1)** at $x$ if
--
--   $$\langle F(x - \gamma^k r(x)), r(x) \rangle \ge \sigma \|r(x)\|^2. \tag{2.1}$$
--
--   Algorithm 2.1 tests $k = 0, 1, 2, \dots$ and takes the first $k$ satisfying (2.1); the trial point $x - \gamma^k r(x)$ then becomes the point $z^i$ that defines the separating hyperplane.
--
--   **Formalization Note** The parameters $\gamma, \sigma \in (0, 1)$ of Algorithm 2.1 are hypotheses of the theorems, not part of this definition.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 767, Algorithm 2.1, Eq. (2.1)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_residual

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- The Armijo-type linesearch condition (2.1) of Algorithm 2.1 (Solodov–Svaiter, p. 767) at the
point `x` and the integer `k`:
`⟨F(x − γᵏ r(x)), r(x)⟩ ≥ σ ‖r(x)‖²`. -/
def ArmijoHolds {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (gamma sigma : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : Prop :=
  sigma * ‖residual F C x‖ ^ 2 ≤ ⟪F (x - gamma ^ k • residual F C x), residual F C x⟫_ℝ

end SolodovSvaiterVI.Alg21


