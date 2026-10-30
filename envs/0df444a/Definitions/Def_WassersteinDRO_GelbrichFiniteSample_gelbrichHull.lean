-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichHull
-- name    : WassersteinDRO_GelbrichFiniteSample_gelbrichHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:58:12.0946+00:00
-- url     : https://prove2.me/theorems/23206df0-bc93-46e4-90a5-ca9e54cd5b71
-- title:
--   Gelbrich hull $\mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma)$
-- statement:
--   Let $\Xi \subseteq \mathbb R^m$, $\varepsilon \in \mathbb R$, $\widehat\mu \in \mathbb R^m$ and let $\widehat\Sigma$ be an $m \times m$ matrix. The **Gelbrich hull** is
--
--   $$\mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma) = \Big\{ \mathbb Q \in \mathcal P(\Xi) : \big(\mathbb E^{\mathbb Q}[\xi], \, \mathbb E^{\mathbb Q}[(\xi - \mathbb E^{\mathbb Q}[\xi])(\xi - \mathbb E^{\mathbb Q}[\xi])^\top]\big) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma) \Big\},$$
--
--   where $\mathcal P(\Xi)$ is the family of probability distributions supported on $\Xi$. Only distributions with finite second moments have a covariance matrix, so only those can belong to the hull.
--
--   The Gelbrich hull is the ambiguity set of the Gelbrich risk; it depends on the distribution only through its first two moments.
--
--   **Formalization Note** Membership is written as: $\mathbb Q$ is a probability measure with $\mathbb Q(\Xi^{\mathrm c}) = 0$, and there are $\mu, \Sigma$ such that $\mathbb Q$ has mean $\mu$ and covariance $\Sigma$ and $(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$. The hull is defined as in Definition 2, not as the union (17), which is a separate item.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Definition 2 (Gelbrich hull), p. 17

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The Gelbrich hull `G_ε(µ̂, Σ̂)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Definition 2 (Gelbrich hull), p. 17: "The Gelbrich hull is given by
G_ε(µ̂, Σ̂) = {Q ∈ P(Ξ) : (E^Q[ξ], E^Q[(ξ − E^Q[ξ])(ξ − E^Q[ξ])⊤]) ∈ U_ε(µ̂, Σ̂)}." Here P(Ξ) is
"the family of all probability distributions supported on Ξ" (§1, p. 6).

`gelbrichHull Ξ ε µ̂ Σ̂` is the set of probability measures `Q` on `ℝ^m` with `Q(Ξᶜ) = 0` that
have finite second moments and whose mean vector and covariance matrix `(µ, Σ)` lie in
`U_ε(µ̂, Σ̂)`.

**Formalization Note.** The pre-image under the mean-covariance projection is written as "there are
`µ, Σ` such that `Q` has mean `µ` and covariance `Σ`, and `(µ, Σ) ∈ U_ε(µ̂, Σ̂)`"; the mean and
covariance are unique, so this is the same set. Finite second moments are part of "has covariance
matrix Σ" (`HasMeanCov`): a distribution without a covariance matrix has no image under the
projection and is not in the hull. "Supported on Ξ" is `Q(Ξᶜ) = 0`. The hull is defined as in
Definition 2, not as the union (17), which is a separate theorem. -/
def gelbrichHull {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | IsProbabilityMeasure Q ∧ Q Ξᶜ = 0 ∧
    ∃ μ Sig, HasMeanCov Q μ Sig ∧ (μ, Sig) ∈ uncertaintySet ε μh Sigh}

end WassersteinDRO.GelbrichFiniteSample


