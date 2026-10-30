-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
-- name    : WassersteinDRO_GelbrichFiniteSample_HasMeanCov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:37.653798+00:00
-- url     : https://prove2.me/theorems/d0f3d7da-8532-4cf0-91b2-473d8f3d9f56
-- title:
--   $\mathbb Q$ has mean vector $\mu$ and covariance matrix $\Sigma$
-- statement:
--   A distribution $\mathbb Q$ on $\mathbb R^m$ **has mean vector $\mu$ and covariance matrix $\Sigma$** if
--
--   1. $\xi$ has a finite second moment under $\mathbb Q$, i.e. $\int \|\xi\|_2^2 \, \mathbb Q(\mathrm d\xi) < \infty$;
--   2. $\mathbb E^{\mathbb Q}[\xi] = \mu$;
--   3. $\mathbb E^{\mathbb Q}[(\xi - \mu)(\xi - \mu)^\top] = \Sigma$.
--
--   This is the hypothesis on the true distribution in Theorem 21 and the membership condition of the Chebyshev ambiguity set $\mathcal P(\Xi, \mu, \Sigma)$.
--
--   **Formalization Note** Clause 1 makes explicit what "has a covariance matrix" presupposes. Without it, Lean's Bochner integral would assign mean $0$ and covariance $0$ to every heavy-tailed distribution.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 21, p. 23 ("has mean vector µ and covariance matrix Σ"); §2.3, p. 18 (P(Ξ, µ, Σ)); Definition 2, p. 17

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_meanVec
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_covMat

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **"`Q` has mean vector `µ` and covariance matrix `Σ`."**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 21, p. 23 ("the unknown true distribution P has mean vector µ and covariance
matrix Σ"); §2.3, p. 18 (the Chebyshev ambiguity set of "distributions on Ξ with mean vector µ and
covariance matrix Σ"); Definition 2, p. 17.

`HasMeanCov Q µ Σ` holds when `ξ` has finite second moment under `Q` (`∫ ‖ξ‖₂² dQ < ∞`), the mean
`E^Q[ξ]` equals `µ`, and the covariance `E^Q[(ξ − µ)(ξ − µ)⊤]` equals `Σ`.

**Formalization Note.** The finite-second-moment clause (`MemLp id 2 Q`) is the presupposition of
"has covariance matrix Σ" made explicit: without it the Bochner integrals in `meanVec` and
`covMat` would return `0` for a heavy-tailed `Q`, which would then "have mean 0 and covariance
0". -/
def HasMeanCov {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) (μ : EuclideanSpace ℝ (Fin m))
    (Sig : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  MemLp (fun ξ => ξ) 2 Q ∧ meanVec Q = μ ∧ covMat Q = Sig

end WassersteinDRO.GelbrichFiniteSample


