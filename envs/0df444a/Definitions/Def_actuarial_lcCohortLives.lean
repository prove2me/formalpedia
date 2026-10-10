-- Prove2me | Definitions.Def_actuarial_lcCohortLives
-- name    : actuarial_lcCohortLives
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:28:54.296963+00:00
-- url     : https://prove2.me/theorems/327e567c-755d-4442-ae38-7c59ddb863c8
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortLives
-- statement:
--   Expected survivors are initial exposed lives times the cohort survival probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_n=l_0{}_np_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

namespace ActuarialValuation

noncomputable def lcCohortLives (initial : ℝ) (q : ℕ → ℝ) (n : ℕ) : ℝ := initial * lcCohortSurvival q n

end ActuarialValuation


