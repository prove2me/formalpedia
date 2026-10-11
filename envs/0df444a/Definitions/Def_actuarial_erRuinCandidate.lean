-- Prove2me | Definitions.Def_actuarial_erRuinCandidate
-- name    : actuarial_erRuinCandidate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:47:56.355038+00:00
-- url     : https://prove2.me/theorems/771eca71-f829-4396-ab20-9f505434d646
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuinCandidate
-- statement:
--   Closed-form ultimate ruin candidate for a classical compound Poisson model with Exp(beta) losses. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Closed-form ultimate ruin candidate for a classical compound} \\ \text{Poisson model with Exp(beta) losses.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity
import Definitions.Def_actuarial_erAdjustment

namespace ActuarialValuation

noncomputable def erRuinCandidate (lambda premium beta initial : ℝ) : ℝ := erTrafficIntensity lambda premium beta * Real.exp (-(erAdjustment lambda premium beta)*initial)

end ActuarialValuation


