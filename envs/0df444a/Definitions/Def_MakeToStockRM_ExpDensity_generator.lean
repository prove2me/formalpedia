-- Prove2me | Definitions.Def_MakeToStockRM_ExpDensity_generator
-- name    : MakeToStockRM_ExpDensity_generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:34:49.038891+00:00
-- url     : https://prove2.me/theorems/8ad7591a-5b8a-4e40-9fd8-611798d062f4
-- title:
--   Generator $\Gamma$ of the inventory/log-price diffusion and its formal adjoint
-- statement:
--   Points of the plane are written $z=(x,y)$, where $x$ is the inventory level and $y$ the (shifted) natural logarithm of the price. For $f:\mathbb R^2\to\mathbb R$ write $\partial_x f$ and $\partial_y f$ for its partial derivatives.
--
--   Let $\theta\in\mathbb R$ be the drift of the inventory, $\sigma>0$ and $\delta>0$ the diffusion coefficients of inventory and log-price, and $\varrho\in(-1,1)$ their correlation. The infinitesimal generator of the limiting diffusion $(\mathcal X,\mathcal Y)$ is the second-order operator
--
--   $$
--   \Gamma f=\theta\,\frac{\partial f}{\partial x}+\frac{\sigma^2}{2}\,\frac{\partial^2 f}{\partial x^2}+\sigma\delta\varrho\,\frac{\partial^2 f}{\partial x\,\partial y}+\frac{\delta^2}{2}\,\frac{\partial^2 f}{\partial y^2}.
--   $$
--
--   Its covariance matrix is $\Sigma=\begin{pmatrix}\sigma^2&\sigma\delta\varrho\\ \sigma\delta\varrho&\delta^2\end{pmatrix}$ and its drift is $(\theta,0)$. Because the coefficients are constant, the formal adjoint (the operator obtained by integrating by parts against a density) is
--
--   $$
--   \Gamma^{*} p=-\theta\,\frac{\partial p}{\partial x}+\frac{\sigma^2}{2}\,\frac{\partial^2 p}{\partial x^2}+\sigma\delta\varrho\,\frac{\partial^2 p}{\partial x\,\partial y}+\frac{\delta^2}{2}\,\frac{\partial^2 p}{\partial y^2}.
--   $$
--
--   $\Gamma$ is the operator in the basic adjoint relation (43) of the paper, and $\Gamma^*$ is the operator whose null space contains the stationary density in the interior of the region.
--
--   **Formalization Note** Partial derivatives are the Fréchet derivative applied to $(1,0)$ and $(0,1)$ (`partialX`, `partialY`); the mixed partial is written $\partial_x(\partial_y f)$ (`partialX (partialY f)`), which equals $\partial_y(\partial_x f)$ for $C^2$ functions. For a non-differentiable function Lean's `fderiv` is $0$, so these operators are only meaningful on $C^2$ functions, which is how every theorem of the mission uses them. The adjoint $\Gamma^*$ is not written in the paper; it is recorded here because it is the interior part of (43) after integration by parts.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 865, §4.1 (generator Γ below (31)); drift and covariance from p. 865, end of §3 (below (28)–(30))

import Mathlib

namespace MakeToStockRM.ExpDensity

/-- Partial derivative `∂f/∂x` of `f : ℝ × ℝ → ℝ` at `z = (x, y)`: the Fréchet derivative applied to `(1, 0)`. -/
noncomputable def partialX (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (1, 0)

/-- Partial derivative `∂f/∂y` of `f : ℝ × ℝ → ℝ` at `z = (x, y)`: the Fréchet derivative applied to `(0, 1)`. -/
noncomputable def partialY (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (0, 1)

/-- The generator `Γ = θ ∂/∂x + (σ²/2) ∂²/∂x² + σδϱ ∂²/∂x∂y + (δ²/2) ∂²/∂y²` of the
inventory/log-price diffusion `(𝒳, 𝒴)` (Caldentey–Wein 2006, p. 865). The mixed partial is
`∂/∂x (∂f/∂y)`. -/
noncomputable def generator (θ σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  θ * partialX f z + σ ^ 2 / 2 * partialX (partialX f) z
    + σ * δ * ϱ * partialX (partialY f) z + δ ^ 2 / 2 * partialY (partialY f) z

/-- The formal adjoint `Γ* = −θ ∂/∂x + (σ²/2) ∂²/∂x² + σδϱ ∂²/∂x∂y + (δ²/2) ∂²/∂y²` of `Γ`
(constant coefficients: only the sign of the first-order term changes). -/
noncomputable def adjointGenerator (θ σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  -θ * partialX f z + σ ^ 2 / 2 * partialX (partialX f) z
    + σ * δ * ϱ * partialX (partialY f) z + δ ^ 2 / 2 * partialY (partialY f) z

end MakeToStockRM.ExpDensity


