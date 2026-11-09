-- Prove2me | Definitions.Def_CubeSampling_observe
-- name    : CubeSampling_observe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:30.387717+00:00
-- url     : https://prove2.me/theorems/983c04df-d384-44ca-85b8-0d4c9c683dec
-- title:
--   Observations $Y_i = f_\theta(X_i) + \xi_i$ of model (1)
-- statement:
--   Given an orthonormal family $\Phi$, a coefficient vector $\theta \in \mathbb R^m$, inputs $X_i$ and noise $\xi_i$, the **observations** of model (1) are the pairs $(X_i, Y_i)$, $i = 1,\dots,n$, with
--   $$
--   Y_i = f_\theta(X_i) + \xi_i, \qquad f_\theta = \theta^\top\Phi = \sum_{j=1}^m \theta_j \varphi_j .
--   $$
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, (1), p.3

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The observations of model (1) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3): from inputs and noise `(X_i, ξ_i)` and a
coefficient vector `θ ∈ ℝ^m`, the data `(X_i, Y_i)` with `Y_i = f_θ(X_i) + ξ_i`,
`f_θ = θ^⊤ Φ_V = ∑_j θ_j φ_j`. -/
def observe {d m n : ℕ} (Φ : Fin m → Cube d → ℝ) (θ : Fin m → ℝ) (ω : Fin n → Cube d × ℝ) :
    Fin n → Cube d × ℝ :=
  fun i => ((ω i).1, ∑ j, θ j * Φ j (ω i).1 + (ω i).2)

end CubeSampling


