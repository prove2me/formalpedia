-- Prove2me | Definitions.Def_actuarial_siVaryingAccum
-- name    : actuarial_siVaryingAccum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:16.722981+00:00
-- url     : https://prove2.me/theorems/0b33991f-35bb-449b-9608-dc96316fe3dd
-- title:
--   Finite-scenario investment returns and fixed random rates: siVaryingAccum
-- statement:
--   Actual sample path of product of potentially differing annual gross returns. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S_n=(1+I)^n,\quad \mathbb{E}[S_n]=\sum_{\omega}p_{\omega}(1+I_{\omega})^n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrowth

namespace ActuarialValuation

noncomputable def siVaryingAccum (rates : ℕ → ℝ) (years : ℕ) : ℝ := ∏ j ∈ Finset.range years, siGrowth (rates j)

end ActuarialValuation


