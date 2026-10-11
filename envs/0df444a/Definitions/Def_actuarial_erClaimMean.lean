-- Prove2me | Definitions.Def_actuarial_erClaimMean
-- name    : actuarial_erClaimMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:44:59.261327+00:00
-- url     : https://prove2.me/theorems/4aa76b9b-610f-41a6-ab69-bf5207018fa8
-- title:
--   Expected aggregate claims and positive safety loading: erClaimMean
-- statement:
--   Expected claim size under an exponential severity distribution with rate beta>0. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Expected claim size under an exponential severity distribution} \\ \text{with rate beta>0.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ActuarialValuation

noncomputable def erClaimMean (beta : ℝ) : ℝ := 1/beta

end ActuarialValuation


