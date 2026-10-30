-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_projMat
-- name    : WainwrightHDS_NucNorm_projMat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:28:52.678965+00:00
-- url     : https://prove2.me/theorems/881c6b37-8914-464d-8282-a88c65366494
-- title:
--   Matrix $P_{\mathbb U}$ of the orthogonal projection onto a subspace $\mathbb U\subseteq\mathbb R^d$
-- statement:
--   For a linear subspace $\mathbb U\subseteq\mathbb R^d$, let $\Pi_{\mathbb U}$ be the Euclidean orthogonal projection onto $\mathbb U$. Its matrix in the standard basis is the $d\times d$ matrix $P_{\mathbb U}$ with
--
--   $$
--   P_{\mathbb U}\,z \;=\; \Pi_{\mathbb U}(z) \qquad\text{for all } z\in\mathbb R^d .
--   $$
--
--   It is the building block of the projections onto the matrix subspaces $\mathbb M$, $\mathbb M^\perp$, $\overline{\mathbb M}$ and $\overline{\mathbb M}^\perp$ used in the cone constraint (10.15).
--
--   **Formalization Note** Defined by converting Mathlib's `Submodule.starProjection` to a matrix.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §9.2, p. 269 (PDF p. 289), Eq. (9.20) (projections), used in Eq. (10.15), p. 319 (PDF p. 339)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **Matrix of the orthogonal projection onto a subspace** `𝕌 ⊆ ℝ^d`: the `d × d` matrix `P_𝕌`
with `P_𝕌 z = Π_𝕌(z)` for every `z ∈ ℝ^d`, where `Π_𝕌` is the Euclidean orthogonal projection
(Mathlib's `Submodule.starProjection`). Auxiliary to the projections of
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, pp. 318–319 (PDF pp. 338–339), (10.15) ("Δ̂_𝕄̄ denotes the projection of the matrix
Δ̂ onto the subspace 𝕄̄"), with projections as in (9.20), p. 269 (PDF p. 289).

Formalization Note: obtained by inverting `Matrix.toEuclideanLin` (matrix ↔ linear map on
`EuclideanSpace ℝ (Fin d)` in the standard basis). -/
noncomputable def projMat {d : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.toEuclideanLin.symm
    ((U.starProjection : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))

end WainwrightHDS.NucNorm


