-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_meanVec
-- name    : WassersteinDRO_GelbrichFiniteSample_meanVec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:55:39.344071+00:00
-- url     : https://prove2.me/theorems/e8fd1567-f4ab-47a2-a4ce-c371ca11cd1e
-- title:
--   Mean vector $\mathbb E^{\mathbb Q}[\xi]$
-- statement:
--   For a distribution $\mathbb Q$ on $\mathbb R^m$, the **mean vector** is $\mathbb E^{\mathbb Q}[\xi] = \int \xi \, \mathbb Q(\mathrm d\xi) \in \mathbb R^m$.
--
--   It is the first component of the mean-covariance projection in the definition of the Gelbrich hull.
--
--   **Formalization Note** This is the Bochner integral, which is $0$ for a non-integrable $\xi$. It only enters statements through "has mean vector $\mu$ and covariance matrix $\Sigma$", which requires finite second moments, so the default value never occurs there.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Definition 2, p. 17 (mean component of the projection); Theorem 21, p. 23

import Mathlib

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The mean vector `E^Q[ξ]` of a distribution on `ℝ^m`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Definition 2, p. 17 (the first component `E^Q[ξ]` of the mean-covariance projection); the
"mean vector µ" of Theorem 21, p. 23.

`meanVec Q = ∫ ξ dQ(ξ) ∈ ℝ^m`.

**Formalization Note.** This is the Bochner integral, which returns `0` when `ξ` is not
`Q`-integrable. It is only ever used through `HasMeanCov`, which requires finite second moments
(hence integrability under a probability measure), so the junk value never enters a statement. -/
noncomputable def meanVec {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) :=
  ∫ ξ, ξ ∂Q

end WassersteinDRO.GelbrichFiniteSample


