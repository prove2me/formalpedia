-- Prove2me | Definitions.Def_WassKF_Bisect_Delta
-- name    : WassKF_Bisect_Delta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:03.682518+00:00
-- url     : https://prove2.me/theorems/6741311d-6480-40f3-ac82-13fa102af347
-- title:
--   Algorithm 1, p. 6 — the duality-gap estimate Δ(γ) = γ(ρ² − Tr[Σ]) − ⟨L(γ), D⟩ + γ²⟨(γI_d − D)⁻¹, Σ⟩
-- statement:
--   With $\Sigma$, $D$, $\rho$ and $L(\gamma) = \gamma^2(\gamma I_d - D)^{-1}\Sigma(\gamma I_d - D)^{-1}$ as above, Algorithm 1 measures the progress of a trial multiplier $\gamma$ by
--   $$
--   \Delta(\gamma) = \gamma\big(\rho^2 - \mathrm{Tr}[\Sigma]\big) - \big\langle L(\gamma), D\big\rangle + \gamma^2\big\langle (\gamma I_d - D)^{-1}, \Sigma\big\rangle ,
--   $$
--   with $\langle A,B\rangle = \mathrm{Tr}[A^\top B]$. The first and last terms form the Lagrangian dual objective of (7b) at $\gamma$, so $\Delta(\gamma)$ is the gap between a dual bound and the primal value of $L(\gamma)$; the algorithm stops once it falls below the tolerance $\varepsilon$.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 6, Algorithm 1 (line 'Set Δ')

import Mathlib
import Definitions.Def_WassKF_Bisect_Lgamma

open Matrix

namespace WassKF.Bisect

/-- The duality-gap estimate `Δ` of Algorithm 1 (p. 6):
`Δ(γ) = γ(ρ² − Tr[Σ]) − ⟨L(γ), D⟩ + γ² ⟨(γI_d − D)⁻¹, Σ⟩`, with `⟨A, B⟩ = Tr[AᵀB]` and
`L(γ) = γ²(γI_d − D)⁻¹Σ(γI_d − D)⁻¹` (`Lgamma`). -/
noncomputable def Delta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma D : Matrix ι ι ℝ) (ρ γ : ℝ) : ℝ :=
  γ * (ρ ^ 2 - Sigma.trace) - ((Lgamma Sigma D γ)ᵀ * D).trace +
    γ ^ 2 * (((γ • (1 : Matrix ι ι ℝ) - D)⁻¹)ᵀ * Sigma).trace

end WassKF.Bisect


