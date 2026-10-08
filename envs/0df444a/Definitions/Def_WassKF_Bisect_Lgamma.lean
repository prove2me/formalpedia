-- Prove2me | Definitions.Def_WassKF_Bisect_Lgamma
-- name    : WassKF_Bisect_Lgamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:53.008985+00:00
-- url     : https://prove2.me/theorems/d1bd78fc-a30c-4977-a19a-ceddf7765a93
-- title:
--   Algorithm 1 and App. A.3, pp. 6, 13 — the candidate L(γ) = γ²(γI_d − D)⁻¹Σ(γI_d − D)⁻¹
-- statement:
--   For $\Sigma, D \in \mathbb{S}^d$ and a scalar $\gamma$ with $\gamma I_d \succ D$, the candidate solution of the direction-finding subproblem (7b) associated with the multiplier $\gamma$ is
--   $$
--   L(\gamma) = \gamma^2\,(\gamma I_d - D)^{-1}\,\Sigma\,(\gamma I_d - D)^{-1}.
--   $$
--   It is the maximizer of the Lagrangian of (7b) for the multiplier $\gamma$ (Lemma A.1), and the matrix that each pass of Algorithm 1 computes and eventually outputs.
--
--   **Formalization Note** Mathlib's matrix inverse is the zero matrix when $\gamma I_d - D$ is singular; statements using `Lgamma` assume $\gamma I_d \succ D$.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 6, Algorithm 1 (line 'Set L'); p. 13, App. A.3, proof of Theorem 3.2

import Mathlib

open Matrix

namespace WassKF.Bisect

/-- The candidate solution of the direction-finding subproblem (7b) at the multiplier `γ`,
as set in Algorithm 1 (p. 6) and in App. A.3 (p. 13):
`L(γ) = γ² (γI_d − D)⁻¹ Σ (γI_d − D)⁻¹`. `⁻¹` is Mathlib's matrix inverse (the zero matrix when
`γI_d − D` is singular); every statement using `Lgamma` assumes `γI_d − D ≻ 0`. -/
noncomputable def Lgamma {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma D : Matrix ι ι ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sigma * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹)

end WassKF.Bisect


