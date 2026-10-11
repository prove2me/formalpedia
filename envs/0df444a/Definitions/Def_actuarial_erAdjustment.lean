-- Prove2me | Definitions.Def_actuarial_erAdjustment
-- name    : actuarial_erAdjustment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:46:38.270704+00:00
-- url     : https://prove2.me/theorems/6188208b-0fdf-4daf-a2eb-4c70ef7cf0c5
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erAdjustment
-- statement:
--   Positive Lundberg exponent for strictly profitable exponential claims. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Positive Lundberg exponent for strictly profitable exponential} \\ \text{claims.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ActuarialValuation

noncomputable def erAdjustment (lambda premium beta : ℝ) : ℝ := beta-lambda/premium

end ActuarialValuation


