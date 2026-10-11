-- Prove2me | Definitions.Def_actuarial_exDensity
-- name    : actuarial_exDensity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:52.4141+00:00
-- url     : https://prove2.me/theorems/c29ea7c7-178c-4126-911c-f62c7b8b7523
-- title:
--   Positive-shape generalized Pareto survival and severity density: exDensity
-- statement:
--   GPD severity density derived from survival and hazard. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_exHazard

namespace ActuarialValuation

noncomputable def exDensity (xi sigma x : ℝ) : ℝ := exSurvival xi sigma x*exHazard xi sigma x

end ActuarialValuation


