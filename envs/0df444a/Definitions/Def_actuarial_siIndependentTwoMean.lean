-- Prove2me | Definitions.Def_actuarial_siIndependentTwoMean
-- name    : actuarial_siIndependentTwoMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:39.505019+00:00
-- url     : https://prove2.me/theorems/26a06d6c-6d15-4f60-941d-c4ae542ab945
-- title:
--   Independent annual returns on actual product scenarios: siIndependentTwoMean
-- statement:
--   Genuine product-law two-year mean with a separate independent scenario for each year. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def siIndependentTwoMean {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : ℝ := ∑ a : Fin m, ∑ b : Fin n, (p a*q b)*(siGrowth (r a)*siGrowth (s b))

end ActuarialValuation


