-- Prove2me | Definitions.Def_AlwaysValidInference_Efficiency_MixingDistribution
-- name    : AlwaysValidInference_Efficiency_MixingDistribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:38:55.090874+00:00
-- url     : https://prove2.me/theorems/09e65890-4f73-4d9b-ba73-220f64275c31
-- title:
--   Continuous positive-density mixing distributions
-- statement:
--   For a parameter domain $\Theta$, a mixing distribution is specified by a density $h$ continuous and strictly positive everywhere on $\Theta$, with $\int_\Theta h(\theta)\,d\theta=1$. Its probability measure is $H(d\theta)=h(\theta)\mathbf1_\Theta(\theta)\,d\theta$. Density values outside the domain are irrelevant. No finite support, conjugate form, or compactness condition is imposed. This definition is independent of the observation family.
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §5.2, p. 18 (PDF page = printed page).

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace AlwaysValidInference.Efficiency

/-- A probability density continuous and strictly positive on its whole domain.
Its values outside the domain do not affect the distribution. -/
structure MixingDistribution (D : Set ℝ) where
  density : ℝ → ℝ
  continuous : ContinuousOn density D
  positive : ∀ θ ∈ D, 0 < density θ
  normalized : ∫⁻ θ in D, ENNReal.ofReal (density θ) = 1

noncomputable def MixingDistribution.law {D : Set ℝ}
    (H : MixingDistribution D) : Measure ℝ :=
  (volume.restrict D).withDensity (fun θ => ENNReal.ofReal (H.density θ))

end AlwaysValidInference.Efficiency


