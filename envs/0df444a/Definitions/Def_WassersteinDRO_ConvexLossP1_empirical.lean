-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_empirical
-- name    : WassersteinDRO_ConvexLossP1_empirical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:56.244121+00:00
-- url     : https://prove2.me/theorems/fac9f042-8106-413b-9792-0aa13d184791
-- title:
--   Empirical distribution $\widehat{\mathbb P}_N$
-- statement:
--   Let $E$ be a measurable space and let $\widehat\xi_1, \dots, \widehat\xi_N \in E$ be training samples. The **empirical distribution** is the uniform distribution on the samples,
--   $$\widehat{\mathbb P}_N = \frac1N \sum_{i=1}^N \delta_{\widehat\xi_i},$$
--   where $\delta_{\widehat\xi_i}$ is the Dirac point mass at $\widehat\xi_i$. Repeated samples are allowed and receive the summed weight.
--
--   It is the nominal distribution of the data-driven problems in the paper and the centre of the Wasserstein ball in Theorem 10.
--
--   **Formalization Note** The samples are indexed by `Fin N`. For $N = 0$ the formula gives the zero measure, not a probability measure; every statement using it assumes $N \ge 1$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Example 1 (1), eq. (3), p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The empirical distribution `P̂_N`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Example 1 (1), eq. (3), p. 2: "P̂N = (1/N) Σ_{i=1}^N δ_{ξ̂i}, where δ_{ξ̂i} denotes the Dirac
point mass at the i-th training sample ξ̂i."

`empirical ξhat` is `N⁻¹ • ∑ᵢ δ_{ξhat i}` for the samples `ξhat : Fin N → E`. Repeated samples are
allowed (they receive the summed weight).

**Formalization Note.** For `N = 0` this is the zero measure, not a probability measure; every
statement that uses it assumes `0 < N`, as the paper's `N` training samples do. -/
noncomputable def empirical {E : Type*} [MeasurableSpace E] {N : ℕ} (ξhat : Fin N → E) :
    Measure E :=
  ((N : ENNReal)⁻¹) • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.ConvexLossP1


