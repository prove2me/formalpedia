-- Prove2me | Definitions.Def_StochKriging_Unbiased_Predictor
-- name    : StochKriging_Unbiased_Predictor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:46.337541+00:00
-- url     : https://prove2.me/theorems/2fd34f41-93f1-4023-a29d-4ae60fb95a5a
-- title:
--   Theorem 1, p. 366 — the estimated intrinsic covariance Σ̂_ε and the plug-in stochastic kriging predictor (13)
-- statement:
--   In the setting of the stochastic kriging model (outputs $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$, design $(\mathbf x_i,n_i)_{i=1}^k$, sample means $\bar{\mathcal Y}(\mathbf x_i)$ and sample variances $\mathcal S^2(\mathbf x_i)$), the intrinsic variance at a design point is estimated by $\widehat{\mathsf V}(\mathbf x_i)=\mathcal S^2(\mathbf x_i)$ (p. 365), and the estimated intrinsic covariance matrix is
--   $$\widehat\Sigma_\varepsilon=\mathrm{Diag}\big\{\widehat{\mathsf V}(\mathbf x_1)/n_1,\ \widehat{\mathsf V}(\mathbf x_2)/n_2,\ \dots,\ \widehat{\mathsf V}(\mathbf x_k)/n_k\big\}.$$
--   The **plug-in stochastic kriging predictor** of $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$ is display (13):
--   $$\widehat{\widehat{\mathsf Y}}(\mathbf x_0)=\beta_0+\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top\big[\Sigma_{\mathsf M}+\widehat\Sigma_\varepsilon\big]^{-1}\big(\bar{\mathcal Y}-\beta_0\mathbf 1_k\big),$$
--   where $\mathbf 1_k$ is the $k\times1$ vector of ones. Only the intrinsic covariance is estimated: $\beta_0$, $\Sigma_{\mathsf M}$ and $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)$ are the true ones. It is a random variable, since $\bar{\mathcal Y}$ and $\widehat\Sigma_\varepsilon$ are computed from the same simulation replications.
--
--   This is the predictor whose unbiasedness is the mission's goal.
--
--   **Formalization Note** The inverse is Mathlib's `Matrix.inv`, which returns $0$ on a singular matrix. Under Assumption 1 (positive definite $\Sigma_{\mathsf M}$ at distinct design points) and $n_i\ge2$ (so $\widehat\Sigma_\varepsilon$ is positive semidefinite), $\Sigma_{\mathsf M}+\widehat\Sigma_\varepsilon$ is invertible at every outcome, so the junk value is never reached in the theorems.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 366, Theorem 1, display (13); p. 365, §3.1 (V̂(x_i) = S²(x_i) at design points)

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.Unbiased

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

/-- Theorem 1 (p. 366): `Σ̂_ε = Diag{V̂(x₁)/n₁, …, V̂(x_k)/n_k}` with `V̂(xᵢ) = 𝒮²(xᵢ)` (p. 365),
computed from the same replications as `𝒴̄`. -/
noncomputable def SigmaEpsHat (β₀ : ℝ) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (x : Fin k → EuclideanSpace ℝ (Fin d))
    (n : Fin k → ℕ) (ω : Ω) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun i => S2 β₀ M ε x n ω i / (n i : ℝ)

/-- Display (13): the plug-in stochastic kriging predictor
`Ŷ̂(x₀) = β₀ + Σ_M(x₀,·)ᵀ [Σ_M + Σ̂_ε]⁻¹ (𝒴̄ − β₀ 1_k)`. -/
noncomputable def predictorHat (P : Measure Ω) (β₀ : ℝ) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (x : Fin k → EuclideanSpace ℝ (Fin d))
    (n : Fin k → ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) (ω : Ω) : ℝ :=
  β₀ + SigmaM0 P M x x₀ ⬝ᵥ
    ((SigmaM P M x + SigmaEpsHat β₀ M ε x n ω)⁻¹ *ᵥ (Ybar β₀ M ε x n ω - fun _ => β₀))

end StochKriging.Unbiased


