-- Prove2me | Definitions.Def_actuarial_exExpectedShortfall
-- name    : actuarial_exExpectedShortfall
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:00:08.978903+00:00
-- url     : https://prove2.me/theorems/84bb9374-c7f3-449e-98e4-3ddb65cbaf7a
-- title:
--   Extreme claim quantiles, threshold stability and expected shortfall: exExpectedShortfall
-- statement:
--   Tail conditional expected severity above a GPD quantile. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   q_p=\frac{\sigma}{\xi}\left((1-p)^{-\xi}-1\right),\quad \text{ES}_p=\frac{q_p+\sigma}{1-\xi}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile

namespace ActuarialValuation

noncomputable def exExpectedShortfall (xi sigma p : ℝ) : ℝ := (exQuantile xi sigma p+sigma)/(1-xi)

end ActuarialValuation


