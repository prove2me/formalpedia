-- Prove2me | Definitions.Def_WassKF_Bisect_hFun
-- name    : WassKF_Bisect_hFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:52.218997+00:00
-- url     : https://prove2.me/theorems/d681f2b8-8b9a-4fe9-8e97-e144d843cdd5
-- title:
--   (8), p. 5 — the auxiliary function h(γ) = ρ² − ⟨Σ, (I_d − γ(γI_d − D)⁻¹)²⟩
-- statement:
--   Fix a covariance matrix $\Sigma \in \mathbb{S}^d_{++}$, a matrix $D \in \mathbb{S}^d$ (in the application $D = \nabla f(S)$) and a radius $\rho > 0$. The auxiliary function of the bisection method is
--   $$
--   h(\gamma) = \rho^2 - \big\langle \Sigma,\ \big(I_d - \gamma(\gamma I_d - D)^{-1}\big)^2 \big\rangle ,
--   $$
--   where $\langle A, B\rangle = \mathrm{Tr}[A^\top B]$ is the trace inner product. Its root $\gamma^\star$ with $\gamma^\star I_d \succ D$ is the optimal Lagrange multiplier of the trace constraint in the direction-finding subproblem (7b); Algorithm 1 locates it by bisection.
--
--   **Formalization Note** `hFun Σ D ρ γ` uses Mathlib's matrix inverse, which returns the zero matrix when $\gamma I_d - D$ is singular, so $h$ is only meaningful for $\gamma I_d \succ D$; every statement using it assumes this.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 5, (8)

import Mathlib

open Matrix

namespace WassKF.Bisect

/-- The auxiliary function (8), p. 5: `h(γ) = ρ² − ⟨Σ, (I_d − γ(γI_d − D)⁻¹)²⟩`, where `D = ∇f(S)`
and `⟨A, B⟩ = Tr[AᵀB]` is the trace inner product. `⁻¹` is Mathlib's matrix inverse (the zero
matrix when `γI_d − D` is singular); every statement using `hFun` assumes `γI_d − D ≻ 0`. -/
noncomputable def hFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma D : Matrix ι ι ℝ) (ρ γ : ℝ) : ℝ :=
  ρ ^ 2 - (Sigmaᵀ * (1 - γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) ^ 2).trace

end WassKF.Bisect


