-- Prove2me | Definitions.Def_CubeSampling_IsOLSRule
-- name    : CubeSampling_IsOLSRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:15.221405+00:00
-- url     : https://prove2.me/theorems/234e68ac-d414-4e69-a048-5ce87e7ea66d
-- title:
--   Ordinary least-squares rule
-- statement:
--   The ordinary least-squares estimator is $\hat\theta_{\mathrm{OLS}} \in \arg\min_{a \in \mathbb R^m} \frac1n\sum_{i=1}^n (Y_i - a^\top\Phi_V(X_i))^2$. An estimator is an **OLS rule** if, on every data set whose empirical covariance $\hat\Sigma_V$ is invertible, it returns the unique least-squares solution
--   $$
--   \hat\theta = \hat\Sigma_V^{-1}\,\frac1n \sum_{i=1}^n Y_i\,\Phi_V(X_i);
--   $$
--   on singular designs its value is unconstrained.
--
--   **Formalization Note** Every least-squares minimizer is an OLS rule in this sense; the class also allows any choice on singular designs.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 2.1, p.7

import Mathlib
import Definitions.Def_CubeSampling_empCov
open Matrix

namespace CubeSampling

/-- An ordinary least-squares rule (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §2.1, p.7: `θ̂_OLS ∈ argmin_a (1/n) ∑_i (Y_i − a^⊤Φ_V(X_i))²`):
on every data set whose empirical covariance `Σ̂_V` is invertible, the estimate is the unique
least-squares solution `Σ̂_V^{−1} (1/n) ∑_i Y_i Φ_V(X_i)`; on singular designs it is unconstrained.

**Formalization Note** This class contains every measurable least-squares minimizer. -/
def IsOLSRule {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (n : ℕ)
    (est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ)) : Prop :=
  ∀ (ω : Fin n → Cube d × ℝ) (u : unitInterval), IsUnit (empCov Φ n (fun i => (ω i).1)).det →
    est (ω, u) = (empCov Φ n (fun i => (ω i).1))⁻¹ *ᵥ
      ((n : ℝ)⁻¹ • ∑ i, (ω i).2 • fun j => Φ j (ω i).1)

end CubeSampling


