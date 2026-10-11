-- Prove2me | Definitions.Def_actuarial_exSurvival
-- name    : actuarial_exSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:58.838156+00:00
-- url     : https://prove2.me/theorems/29ffcba1-0eb7-4926-b5b4-9b428a871318
-- title:
--   Positive-shape generalized Pareto survival and severity density: exSurvival
-- statement:
--   Exact generalized Pareto survival function on positive support. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_exBase

namespace ActuarialValuation

noncomputable def exSurvival (xi sigma x : ℝ) : ℝ := Real.rpow (exBase xi sigma x) (-1/xi)

end ActuarialValuation


