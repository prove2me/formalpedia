-- Prove2me | Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
-- name    : MakeToStockRM_ExpDensity_covMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:35:00.369303+00:00
-- url     : https://prove2.me/theorems/127c4ba7-3be3-4412-9c13-376a68b97359
-- title:
--   Covariance matrix $\Sigma$ of the inventory/log-price diffusion
-- statement:
--   For diffusion coefficients $\sigma,\delta$ and correlation $\varrho$, the covariance matrix of the limiting diffusion $(\mathcal X,\mathcal Y)$ (inventory, log-price) is
--
--   $$
--   \Sigma=\begin{pmatrix}\sigma^2&\sigma\delta\varrho\\ \sigma\delta\varrho&\delta^2\end{pmatrix},
--   $$
--
--   read off from the second-order part of the generator $\Gamma=\theta\partial_x+\tfrac{\sigma^2}{2}\partial_{xx}+\sigma\delta\varrho\partial_{xy}+\tfrac{\delta^2}{2}\partial_{yy}$, which equals $\theta\partial_x+\tfrac12\nabla\cdot(\Sigma\nabla)$.
--
--   $\Sigma$ enters Proposition 2 twice: through the whitening map $T=E^{-1/2}V$ built from its eigen-decomposition $\Sigma=V'EV$, and through the conormal reflection field $\Sigma\vec n$ on the boundary.
--
--   **Formalization Note** A $2\times2$ real matrix indexed by `Fin 2`, first coordinate the inventory $x$, second the log-price $y$. It is positive definite exactly when $\sigma,\delta\neq0$ and $|\varrho|<1$; the theorems assume $\sigma,\delta>0$ and $|\varrho|<1$.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 865 (generator Γ, §4.1); p. 867 ("Let Σ be the covariance matrix of (𝒳, 𝒴)", preamble of Proposition 2)

import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The covariance matrix `Σ = [[σ², σδϱ], [σδϱ, δ²]]` of the diffusion `(𝒳, 𝒴)`, read off from
the generator `Γ` (Caldentey–Wein 2006, p. 865). -/
def covMatrix (σ δ ϱ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ ^ 2, σ * δ * ϱ; σ * δ * ϱ, δ ^ 2]

end MakeToStockRM.ExpDensity


