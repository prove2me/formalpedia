-- Prove2me | Definitions.Def_GaoImpatientMNL_Pricing_GumbelLaw
-- name    : GaoImpatientMNL_Pricing_GumbelLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:00.469804+00:00
-- url     : https://prove2.me/theorems/cfb40535-e2e9-4419-be68-9e7219ecd366
-- title:
--   Location-scale Gumbel random-variable law
-- statement:
--   On a measurable space with measure $P$, a measurable real random variable $X$ has Gumbel law with location $a$ and positive scale $s$ when $P$ is a probability measure and
--   $$P(X\le x)=\exp[-\exp(-(x-a)/s)]\quad(x\in\mathbb R).$$
--   The right side is the published Gumbel CDF, converted to a nonnegative extended-real probability. This general probability-law predicate is independent of the sequential-pricing model. The customer model specializes it to scale one.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, held source.pdf, §§2,4 and Appendix F; PDF pp.6,11–16,45–51 (printed pp.6,11–16,ec8–ec14).

import Mathlib
import Definitions.Def_actuarial_exGumbelMaxCdf

open MeasureTheory
noncomputable section

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT
noncomputable section
namespace ActuarialValuation
noncomputable def exGumbelMaxCdf (location scale x : ℝ) : ℝ := Real.exp (-Real.exp (-(x-location)/scale))
end ActuarialValuation
end
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

/-- General location-scale Gumbel random variable, using the published CDF.
Measurability is explicit; scale is positive and the ambient measure is a probability. -/
def HasGumbelLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (location scale : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable X ∧ 0 < scale ∧
    ∀ x, P {ω | X ω ≤ x} = ENNReal.ofReal (ActuarialValuation.exGumbelMaxCdf location scale x)

end GaoImpatientMNL.Pricing


