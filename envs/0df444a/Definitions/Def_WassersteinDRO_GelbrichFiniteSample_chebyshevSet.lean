-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_chebyshevSet
-- name    : WassersteinDRO_GelbrichFiniteSample_chebyshevSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:37.614693+00:00
-- url     : https://prove2.me/theorems/4b857515-a793-4a17-8c65-0852da4216c5
-- title:
--   Chebyshev ambiguity set $\mathcal P(\Xi, \mu, \Sigma)$
-- statement:
--   Let $\Xi \subseteq \mathbb R^m$, $\mu \in \mathbb R^m$ and let $\Sigma$ be an $m \times m$ matrix. The **Chebyshev ambiguity set** $\mathcal P(\Xi, \mu, \Sigma)$ is the set of all probability distributions $\mathbb Q$ on $\mathbb R^m$ that are supported on $\Xi$ (that is, $\mathbb Q(\mathbb R^m \setminus \Xi) = 0$) and have mean vector $\mu$ and covariance matrix $\Sigma$ (with finite second moments).
--
--   The Gelbrich hull is the union of these sets over $(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$ (eq. (17)).
--
--   **Formalization Note** "Supported on $\Xi$" is encoded as $\mathbb Q(\Xi^{\mathrm c}) = 0$; for the paper's closed $\Xi$ this is the same as $\operatorname{supp} \mathbb Q \subseteq \Xi$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.3, sentence introducing eq. (17), p. 18; P(Ξ) from §1, p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The Chebyshev ambiguity set `P(Ξ, µ, Σ)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.3, p. 18 (the sentence introducing (17)): "If we define P(Ξ, µ, Σ) as the Chebyshev
ambiguity set that contains all distributions on Ξ with mean vector µ and covariance matrix Σ".
"Distributions on Ξ" are the members of P(Ξ), "the family of all probability distributions
supported on Ξ" (§1, p. 6).

`chebyshevSet Ξ µ Σ` is the set of probability measures `Q` on `ℝ^m` with `Q(Ξᶜ) = 0` that have
finite second moments, mean vector `µ` and covariance matrix `Σ`.

**Formalization Note.** "Supported on Ξ" is `Q(Ξᶜ) = 0` (for the paper's closed `Ξ`, this is the
same as `supp Q ⊆ Ξ`). The covariance matrix is written `Sig` because `Σ` is Lean syntax. -/
def chebyshevSet {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (μ : EuclideanSpace ℝ (Fin m))
    (Sig : Matrix (Fin m) (Fin m) ℝ) : Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | IsProbabilityMeasure Q ∧ Q Ξᶜ = 0 ∧ HasMeanCov Q μ Sig}

end WassersteinDRO.GelbrichFiniteSample


