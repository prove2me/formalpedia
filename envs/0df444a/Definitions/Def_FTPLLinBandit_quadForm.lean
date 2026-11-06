-- Prove2me | Definitions.Def_FTPLLinBandit_quadForm
-- name    : FTPLLinBandit_quadForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:10.361253+00:00
-- url     : https://prove2.me/theorems/6b0f651e-bbf3-4a6e-bd5c-662379840891
-- title:
--   Quadratic form $u^\top Mu$
-- statement:
--   For a real $d\times d$ matrix $M$ and a vector $u\in\mathbb R^d$, the **quadratic form** is
--   $$u^\top M u=\sum_{i,j}u_iM_{ij}u_j .$$
--   With $M=\Sigma^{-1}$ it gives the squared Mahalanobis norm $\|u\|^2_{\Sigma^{-1}}=u^\top\Sigma^{-1}u$ used throughout the paper, e.g. in $\hat\theta_t^\top\Sigma_t^{-1}\hat\theta_t$ and in the elliptical densities $P_\Sigma(z)\propto f(\|z\|_{\Sigma^{-1}})$.
--
--   **Formalization Note** The matrix acts on the coordinate vector of $u\in$ `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, p.8; §4, p.9; Theorem 10, p.13

import Mathlib

open Matrix

namespace FTPLLinBandit

/-- **The quadratic form `uᵀ M u`** of a `d × d` real matrix `M` at a vector `u ∈ ℝ^d`. It is used
for `θ̂ᵀ Σ⁻¹ θ̂ = ‖θ̂‖²_{Σ⁻¹}` and for the Mahalanobis norm `‖z‖_{Σ⁻¹} = √(zᵀ Σ⁻¹ z)` throughout
Wei, arXiv:2610.17818 (e.g. Figure 2, p.8; §4, p.9; Theorem 10, p.13).

**Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin d)`; the matrix acts on their
coordinate vectors `WithLp.ofLp u : Fin d → ℝ`, and `⬝ᵥ` is the coordinate dot product. -/
noncomputable def quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  WithLp.ofLp u ⬝ᵥ (M *ᵥ WithLp.ofLp u)

end FTPLLinBandit


