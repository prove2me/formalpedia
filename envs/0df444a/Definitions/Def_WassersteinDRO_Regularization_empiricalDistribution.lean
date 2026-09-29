-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
-- name    : WassersteinDRO_Regularization_empiricalDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:39:58.765709+00:00
-- url     : https://prove2.me/theorems/1b72e42b-db53-43a9-806a-7fc637ea7c6b
-- title:
--   Empirical distribution of $N$ training samples
-- statement:
--   The empirical distribution of $N$ training samples $\hat\xi : \{1,\dots,N\} \to E$ is
--   $\hat P_N = \frac{1}{N}\sum_{i=1}^N \delta_{\hat\xi_i}$, the uniform mixture of Dirac masses at
--   the samples.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Example 1(1), p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The empirical distribution of `N` training samples `ξ̂ : Fin N → E`, Kuhn et al. 2019,
Example 1(1), p. 2: `PN = (1/N) Σ_{i=1}^N δ_{ξ̂ i}`, the uniform mixture of Dirac masses at
the samples. Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Regularization_wassersteinDistance` for why. -/
noncomputable def empiricalDistribution {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξhat : Fin N → E) : Measure E :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.Regularization


