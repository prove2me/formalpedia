-- Prove2me | Definitions.Def_actuarial_exGumbelMaxCdf
-- name    : actuarial_exGumbelMaxCdf
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:00:32.25362+00:00
-- url     : https://prove2.me/theorems/da347963-a227-4ae6-92fe-8438844935a5
-- title:
--   Gumbel and generalized extreme-value maxima: exGumbelMaxCdf
-- statement:
--   Maximum-type Gumbel extreme-loss cumulative distribution. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   G_{\xi}(x)=\exp\left[-\left(1+\xi\frac{x-\mu}{\sigma}\right)^{-1/\xi}\right]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ActuarialValuation

noncomputable def exGumbelMaxCdf (location scale x : ℝ) : ℝ := Real.exp (-Real.exp (-(x-location)/scale))

end ActuarialValuation


