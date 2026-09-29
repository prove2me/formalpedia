-- Prove2me | Definitions.Def_MakeToStockRM_ExpDensity_boundaryTerm
-- name    : MakeToStockRM_ExpDensity_boundaryTerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:36:23.093912+00:00
-- url     : https://prove2.me/theorems/de16d310-90dc-488d-8e5a-a10938d4609d
-- title:
--   Boundary integral $\int_{\partial\Omega}(\Sigma\vec n)\cdot\nabla f\,p\,dl$ of the basic adjoint relation
-- statement:
--   Let $\Sigma$ be the covariance matrix of the inventory/log-price diffusion, $\eta<\xi$ the rejection and idleness boundaries, and $\Omega$ the region (34) between them for $y_{\min}<y<y_{\max}$. For a vector $w=(w_1,w_2)$ and a differentiable $f$, the **conormal flux** of $f$ at $z$ in direction $w$ is
--
--   $$
--   (\Sigma w)\cdot\nabla f(z)=(\sigma^2w_1+\sigma\delta\varrho w_2)\,\partial_x f(z)+(\sigma\delta\varrho w_1+\delta^2w_2)\,\partial_y f(z).
--   $$
--
--   For functions $f$ and $p$ on the plane, the boundary term is the surface integral $\int_{\partial\Omega}(\Sigma\vec n)\cdot\nabla f\;p\;dl$, where $\vec n$ is the inward unit normal of $\partial\Omega$ and $dl$ is arc length. Written out on the four pieces (35), with $\vec n\,dl$ expressed in the parametrization of each piece, it is
--
--   $$
--   \begin{aligned}
--   &\int_{y_{\min}}^{y_{\max}}(\Sigma(1,-\eta'(y)))\cdot\nabla f(\eta(y),y)\,p(\eta(y),y)\,dy
--   +\int_{y_{\min}}^{y_{\max}}(\Sigma(-1,\xi'(y)))\cdot\nabla f(\xi(y),y)\,p(\xi(y),y)\,dy\\
--   &\quad+\int_{\eta(y_{\min})}^{\xi(y_{\min})}(\Sigma(0,1))\cdot\nabla f(x,y_{\min})\,p(x,y_{\min})\,dx
--   +\int_{\eta(y_{\max})}^{\xi(y_{\max})}(\Sigma(0,-1))\cdot\nabla f(x,y_{\max})\,p(x,y_{\max})\,dx .
--   \end{aligned}
--   $$
--
--   On $x=\eta(y)$ the inward unit normal is $(1,-\eta'(y))/\sqrt{1+\eta'(y)^2}$ and $dl=\sqrt{1+\eta'(y)^2}\,dy$, whence $(1,-\eta'(y))\,dy$; similarly on the other pieces. This is the boundary part of the paper's basic adjoint relation (43) with the reflection field $\vec v=\Sigma\vec n$.
--
--   **Formalization Note** `conormalFlux` is `(covMatrix σ δ ϱ *ᵥ ![w.1, w.2]) ⬝ᵥ ![∂ₓf z, ∂ᵧf z]`. The derivatives of the curves are `deriv η`, `deriv ξ`, which are the true derivatives for the $C^1$ curves the theorems assume. The corners of $\partial\Omega$ have zero arc length and are ignored.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, eq. (43) (boundary integral) with the reflection field of Proposition 2; boundary pieces (35), p. 866

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix

namespace MakeToStockRM.ExpDensity

open Matrix

/-- The conormal flux `(Σ w) · ∇f(z)`, with `Σ = covMatrix σ δ ϱ` and `∇f = (∂f/∂x, ∂f/∂y)`; that is,
`(σ² w₁ + σδϱ w₂) ∂f/∂x + (σδϱ w₁ + δ² w₂) ∂f/∂y`. -/
noncomputable def conormalFlux (σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (w : ℝ × ℝ) : ℝ :=
  (covMatrix σ δ ϱ *ᵥ ![w.1, w.2]) ⬝ᵥ ![partialX f z, partialY f z]

/-- The boundary integral `∫_{∂Ω} (Σ n⃗) · ∇f · p dl` over the four pieces (35) of `∂Ω`, with `n⃗`
the inward unit normal and `n⃗ dl` written out in the parametrization of each piece:
`(1, −η'(y)) dy` on `x = η(y)`, `(−1, ξ'(y)) dy` on `x = ξ(y)`, `(0, 1) dx` on `y = y_min`,
`(0, −1) dx` on `y = y_max`. -/
noncomputable def boundaryTerm (σ δ ϱ : ℝ) (η ξ : ℝ → ℝ) (ymin ymax : ℝ)
    (f p : ℝ × ℝ → ℝ) : ℝ :=
  (∫ y in ymin..ymax, conormalFlux σ δ ϱ f (η y, y) (1, -deriv η y) * p (η y, y))
    + (∫ y in ymin..ymax, conormalFlux σ δ ϱ f (ξ y, y) (-1, deriv ξ y) * p (ξ y, y))
    + (∫ x in η ymin..ξ ymin, conormalFlux σ δ ϱ f (x, ymin) (0, 1) * p (x, ymin))
    + (∫ x in η ymax..ξ ymax, conormalFlux σ δ ϱ f (x, ymax) (0, -1) * p (x, ymax))

end MakeToStockRM.ExpDensity


