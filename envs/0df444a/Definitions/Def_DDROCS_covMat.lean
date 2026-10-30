-- Prove2me | Definitions.Def_DDROCS_covMat
-- name    : DDROCS_covMat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:42.708892+00:00
-- url     : https://prove2.me/theorems/163281e9-f3d6-41a7-a16c-c7c8b44ae727
-- title:
--   Covariance matrix $\mathbb E^{\mathbb P}[\tilde u\tilde u^\top] - \mathbb E^{\mathbb P}[\tilde u]\mathbb E^{\mathbb P}[\tilde u^\top]$
-- statement:
--   Let $\mathbb P$ be a measure on $\mathbb R^d$, the law of a random vector $\tilde u$. Its **covariance matrix** is the $d\times d$ matrix
--
--   $$
--   \mathrm{Cov}(\mathbb P) \;=\; \mathbb E^{\mathbb P}[\tilde u\tilde u^\top] - \mathbb E^{\mathbb P}[\tilde u]\,\mathbb E^{\mathbb P}[\tilde u^\top],
--   \qquad
--   \mathrm{Cov}(\mathbb P)_{ij} = \mathbb E^{\mathbb P}[\tilde u_i \tilde u_j] - \mathbb E^{\mathbb P}[\tilde u_i]\,\mathbb E^{\mathbb P}[\tilde u_j].
--   $$
--
--   It is the matrix whose Frobenius distance to the sample covariance $\hat\Sigma$ defines the confidence region $\mathcal P^{CS}$ of Section 8.1.
--
--   **Formalization Note** Written entry by entry as "second moment minus product of means", with Bochner integrals. A Bochner integral is $0$ for a non-integrable integrand; the definition is only used for members of $\mathcal P^{CS}$, which are probability measures concentrated on a ball, so every integrand is bounded and integrable.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 8.1, p. 24 (inside Theorem 9)

import Mathlib
open MeasureTheory

namespace DDROCS

/-- **Covariance matrix of a measure**, `E^P[ũũᵀ] − E^P[ũ]E^P[ũᵀ]`.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 8.1, p. 24
(inside Theorem 9, unnumbered): the matrix `E^P[ũũᵀ] − E^P[ũ]E^P[ũᵀ]` whose Frobenius distance
to `Σ̂` defines `P^CS`.

`covMat P i j = ∫ u_i u_j dP − (∫ u_i dP)(∫ u_j dP)`.

**Formalization Note.** Written exactly as the paper's "second moment minus outer product of the
means", entry by entry, with Bochner integrals over `ℝ^d = EuclideanSpace ℝ (Fin d)`. The Bochner
integral is `0` for a non-integrable integrand; the only use of `covMat` is inside `PCS`, whose
members are probability measures concentrated on a closed ball, for which every such integrand is
bounded and integrable. -/
noncomputable def covMat {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∫ u, u i * u j ∂P) - (∫ u, u i ∂P) * (∫ u, u j ∂P)

end DDROCS


