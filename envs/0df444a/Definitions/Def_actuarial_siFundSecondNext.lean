-- Prove2me | Definitions.Def_actuarial_siFundSecondNext
-- name    : actuarial_siFundSecondNext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:24.796559+00:00
-- url     : https://prove2.me/theorems/53139927-342a-44dc-a49e-089f1b355d08
-- title:
--   Regular contributions and fund first/second-moment recursions: siFundSecondNext
-- statement:
--   Fund second-moment recursion under independent next-year investment gross returns. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def siFundSecondNext (priorSecond priorMean contribution secondGross : ℝ) : ℝ := (priorSecond+2*contribution*priorMean+contribution^2)*secondGross

end ActuarialValuation


