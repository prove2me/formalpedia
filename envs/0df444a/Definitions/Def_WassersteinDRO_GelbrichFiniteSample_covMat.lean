-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_covMat
-- name    : WassersteinDRO_GelbrichFiniteSample_covMat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:05.540991+00:00
-- url     : https://prove2.me/theorems/e05365b7-3a04-4f2d-b91a-4e3ee3a0ac76
-- title:
--   Covariance matrix $\mathbb E^{\mathbb Q}[(\xi - \mathbb E^{\mathbb Q}[\xi])(\xi - \mathbb E^{\mathbb Q}[\xi])^\top]$
-- statement:
--   For a distribution $\mathbb Q$ on $\mathbb R^m$ with mean vector $\mu = \mathbb E^{\mathbb Q}[\xi]$, the **covariance matrix** is the $m \times m$ matrix
--
--   $$\mathbb E^{\mathbb Q}\big[(\xi - \mu)(\xi - \mu)^\top\big], \qquad \text{with entries } \int (\xi_j - \mu_j)(\xi_k - \mu_k) \, \mathbb Q(\mathrm d\xi).$$
--
--   It is the second component of the mean-covariance projection in the definition of the Gelbrich hull.
--
--   **Formalization Note** The entries are Bochner integrals, which are $0$ for non-integrable integrands. The matrix only enters statements through "has mean vector $\mu$ and covariance matrix $\Sigma$", which requires finite second moments.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Definition 2, p. 17 (covariance component of the projection); Theorem 21, p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_meanVec

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The covariance matrix `E^Q[(ξ − E^Q[ξ])(ξ − E^Q[ξ])⊤]` of a distribution on `ℝ^m`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Definition 2, p. 17 (the second component of the mean-covariance projection); the
"covariance matrix Σ" of Theorem 21, p. 23.

`covMat Q` is the `m × m` matrix with entries `∫ (ξ − µ)_j (ξ − µ)_k dQ(ξ)`, where
`µ = meanVec Q`.

**Formalization Note.** The entries are Bochner integrals, which return `0` for non-integrable
integrands. The matrix is only ever used through `HasMeanCov`, which requires finite second
moments, so every entry is a genuine integral there. -/
noncomputable def covMat {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => ∫ ξ, (ξ - meanVec Q) j * (ξ - meanVec Q) k ∂Q

end WassersteinDRO.GelbrichFiniteSample


