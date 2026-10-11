-- Prove2me | Definitions.Def_actuarial_erRuinEquationResidual
-- name    : actuarial_erRuinEquationResidual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:49:27.512212+00:00
-- url     : https://prove2.me/theorems/f9181d04-116f-47df-b195-9bda8b00ecc4
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuinEquationResidual
-- statement:
--   Classical Cramer–Lundberg renewal differential equation residual cψ'-λ(ψ-∫ψf-tail), with the sign convention from claim outgo. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Classical Cramer–Lundberg renewal differential equation} \\ \text{residual cψ'-λ(ψ-∫ψf-tail), with the sign convention from claim} \\ \text{outgo.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail
import Definitions.Def_actuarial_erRuinCandidate
import Definitions.Def_actuarial_erRuinDerivativeRHS
import Definitions.Def_actuarial_erRenewalIntegral

namespace ActuarialValuation

noncomputable def erRuinEquationResidual (lambda premium beta initial : ℝ) : ℝ := premium*erRuinDerivativeRHS lambda premium beta initial-lambda*(erRuinCandidate lambda premium beta initial-erRenewalIntegral lambda premium beta initial-erSeverityTail beta initial)

end ActuarialValuation


