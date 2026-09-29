-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_empiricalDistribution
-- name    : WassersteinDRO_Guarantees_empiricalDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:31:46.540581+00:00
-- url     : https://prove2.me/theorems/73044d0d-4617-48d0-9543-6a789b976bd6
-- title:
--   Empirical distribution of $N$ training samples
-- statement:
--   The empirical distribution of $N$ training samples $\hat\xi : \{1,\dots,N\} \to \mathbb{R}^m$
--   is $\hat P_N = \frac{1}{N}\sum_{i=1}^N \delta_{\hat\xi_i}$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Example 1(1), p. 2

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The empirical distribution of `N` training samples `ξ̂ : Fin N → ℝ^m`, Kuhn et al. 2019,
Example 1(1), p. 2: `PN = (1/N) Σ_{i=1}^N δ_{ξ̂ i}`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def empiricalDistribution {m N : ℕ} (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.Guarantees


