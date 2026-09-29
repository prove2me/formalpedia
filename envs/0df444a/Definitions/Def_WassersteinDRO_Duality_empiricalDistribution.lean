-- Prove2me | Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
-- name    : WassersteinDRO_Duality_empiricalDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:17:05.624285+00:00
-- url     : https://prove2.me/theorems/2dcf09fe-45a2-4709-9223-8cc071b9d6d5
-- title:
--   Empirical distribution of $N$ samples
-- statement:
--   The empirical distribution of $N$ training samples $\hat\xi_1,\dots,\hat\xi_N \in E$ is
--   the uniform mixture of Dirac masses at the samples,
--   $$\hat P_N = \frac{1}{N}\sum_{i=1}^N \delta_{\hat\xi_i}.$$
-- source:
--   Kuhn et al. 2019, Example 1(1), p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The empirical distribution of `N` training samples `ξ̂ : Fin N → E`, Kuhn et al. 2019,
Example 1(1), p. 2: `PN = (1/N) Σ_{i=1}^N δ_{ξ̂ i}`, the uniform mixture of Dirac masses at
the samples. -/
noncomputable def empiricalDistribution {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξhat : Fin N → E) : Measure E :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.Duality


