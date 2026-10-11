-- Prove2me | Definitions.Def_actuarial_siFundStep
-- name    : actuarial_siFundStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:10.036426+00:00
-- url     : https://prove2.me/theorems/1d248413-15c0-4bc9-9b7a-aa16cce4490a
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundStep
-- statement:
--   Actual end-of-year portfolio value after beginning-year contribution and investment return. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   A_{n+1}=(A_n+c)G_{n+1},\quad m_{n+1}=(m_n+c)\bar G
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace ActuarialValuation

noncomputable def siFundStep (fund contribution gross : ℝ) : ℝ := (fund+contribution)*gross

end ActuarialValuation


