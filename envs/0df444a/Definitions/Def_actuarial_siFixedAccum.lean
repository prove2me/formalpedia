-- Prove2me | Definitions.Def_actuarial_siFixedAccum
-- name    : actuarial_siFixedAccum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:58:59.98309+00:00
-- url     : https://prove2.me/theorems/f224a254-b14c-4397-9fa3-8c5825315235
-- title:
--   Finite-scenario investment returns and fixed random rates: siFixedAccum
-- statement:
--   A single random interest rate chosen once then fixed throughout investment horizon. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def siFixedAccum (rate : ℝ) (years : ℕ) : ℝ := (siGrowth rate)^years

end ActuarialValuation


