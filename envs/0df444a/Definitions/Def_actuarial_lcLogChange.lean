-- Prove2me | Definitions.Def_actuarial_lcLogChange
-- name    : actuarial_lcLogChange
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T09:17:43.477978+00:00
-- url     : https://prove2.me/theorems/9b8d8944-0b40-4165-bc4d-2028af778858
-- title:
--   Age-period Lee-Carter log mortality and drift: lcLogChange
-- statement:
--   Mortality's log-rate change is proportional to the change in the common period index. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \log(m_2/m_1)=b(\kappa_2-\kappa_1)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def lcLogChange (b k1 k2 : ℝ) : ℝ := b*(k2-k1)

end ActuarialValuation


