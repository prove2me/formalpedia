-- Prove2me | Definitions.Def_actuarial_erLundbergGap
-- name    : actuarial_erLundbergGap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:47:05.559303+00:00
-- url     : https://prove2.me/theorems/23139085-8aef-4f75-87fb-31b7f4d806ad
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erLundbergGap
-- statement:
--   Lundberg cumulant condition λ(M_X(r)-1)=cr. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Lundberg cumulant condition λ(M\_X(r)-1)=cr.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExponentialMGF

namespace ActuarialValuation

noncomputable def erLundbergGap (lambda premium beta r : ℝ) : ℝ := lambda*(erExponentialMGF beta r-1)-premium*r

end ActuarialValuation


