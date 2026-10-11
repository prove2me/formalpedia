-- Prove2me | Definitions.Def_actuarial_siGrossSecond
-- name    : actuarial_siGrossSecond
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:29.48357+00:00
-- url     : https://prove2.me/theorems/8e0075d3-618a-4fc4-94cd-b03c69a05188
-- title:
--   Independent annual returns on actual product scenarios: siGrossSecond
-- statement:
--   Second moment of one-year gross return. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siGrowth
import Definitions.Def_actuarial_siSecond

namespace ActuarialValuation

noncomputable def siGrossSecond {m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) : ℝ := siSecond p (fun j => siGrowth (r j))

end ActuarialValuation


