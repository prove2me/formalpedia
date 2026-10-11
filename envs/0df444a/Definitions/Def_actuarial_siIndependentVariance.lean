-- Prove2me | Definitions.Def_actuarial_siIndependentVariance
-- name    : actuarial_siIndependentVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:58.981988+00:00
-- url     : https://prove2.me/theorems/c0991d0e-a080-4f40-a8ad-69eab999d115
-- title:
--   Independent annual returns on actual product scenarios: siIndependentVariance
-- statement:
--   Moment-factorized accumulation variance under iid annual investment gross returns. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[G_1G_2]=\mathbb{E}[G_1]\mathbb{E}[G_2]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace ActuarialValuation

noncomputable def siIndependentVariance (meanGross secondGross : ℝ) (years : ℕ) : ℝ := secondGross^years-(meanGross^years)^2

end ActuarialValuation


