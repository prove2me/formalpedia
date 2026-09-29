-- Prove2me | Definitions.Def_CubicNewton_LocalQuad_deltaMeasure
-- name    : CubicNewton_LocalQuad_deltaMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:32:10.257725+00:00
-- url     : https://prove2.me/theorems/2408195c-d46e-4b4f-a5eb-8d7f1e953502
-- title:
--   The local measure $\delta = L\|f'(x)\|/\lambda_n^2(f''(x))$
-- statement:
--   Let $f$ be twice differentiable on $\mathbb{R}^n$ with gradient $f'$ and Hessian $f''$, and let $L > 0$ be the Lipschitz constant of the Hessian. At a point $x$ where $f''(x) \succ 0$ define
--   $$\delta(x) = \frac{L\,\|f'(x)\|}{\lambda_n^2(f''(x))},$$
--   where $\lambda_n$ is the smallest eigenvalue. Along the iterates $x_k$ of the relaxed method (3.5) the paper writes $\delta_k = \delta(x_k)$. It is a scale-free measure of how close $x$ is to a non-degenerate critical point: the local quadratic convergence theorem (Theorem 3) starts from $\delta_0 \le 1/4$.
--
--   **Formalization Note** $\lambda_n$ is `lamMin` (Rayleigh-quotient infimum). The paper uses $\delta$ only where $\lambda_n(f''(x)) > 0$; where $\lambda_n(f''(x)) = 0$ Lean's division returns $0$, and every theorem using $\delta$ either assumes or proves $\lambda_n(f''(x)) > 0$ at the points concerned.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 186, Section 3 (definition of δk after (3.5))

import Mathlib
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.LocalQuad

/-- The quantity `δ = L‖f′(x)‖ / λₙ²(f″(x))` of Nesterov–Polyak 2006, Section 3, p. 186 (defined
there for the iterates, `δ_k = L‖f′(x_k)‖ / λₙ²(f″(x_k))`), with `g x` for `f′(x)`, `H x` for
`f″(x)` and `lamMin` for `λₙ`. The paper uses it only where `f″(x) ≻ 0`, i.e. `0 < lamMin (H x)`;
when `lamMin (H x) = 0` Lean's division returns `0`. -/
noncomputable def deltaMeasure {n : ℕ} (L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  L * ‖g x‖ / CubicNewton.Shared.lamMin (H x) ^ 2

end CubicNewton.LocalQuad


