-- Prove2me | Definitions.Def_actuarial_exCdf
-- name    : actuarial_exCdf
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:13.820056+00:00
-- url     : https://prove2.me/theorems/aa1b5f5c-e79e-4f7e-b175-508f39af6455
-- title:
--   Positive-shape generalized Pareto survival and severity density: exCdf
-- statement:
--   GPD exceedance CDF constructed from its survival function. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S(x)=\left(1+\frac{\xi x}{\sigma}\right)^{-1/\xi}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival

namespace ActuarialValuation

noncomputable def exCdf (xi sigma x : ℝ) : ℝ := 1-exSurvival xi sigma x

end ActuarialValuation


