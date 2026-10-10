-- Prove2me | Definitions.Def_actuarial_lcLogRate
-- name    : actuarial_lcLogRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:15:58.069554+00:00
-- url     : https://prove2.me/theorems/1b0237b4-f54f-4b26-949b-a33712b15a33
-- title:
--   Age-period Lee-Carter log mortality and drift: lcLogRate
-- statement:
--   A one-factor Lee-Carter age-period model describes log mortality by age effect and a period index multiplier. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \log m_{x,t}=a_x+b_x\kappa_t
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def lcLogRate (a b k : ℝ) : ℝ := a + b*k

end ActuarialValuation


