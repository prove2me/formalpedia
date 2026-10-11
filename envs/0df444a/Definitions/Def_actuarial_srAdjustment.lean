-- Prove2me | Definitions.Def_actuarial_srAdjustment
-- name    : actuarial_srAdjustment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:02:18.801991+00:00
-- url     : https://prove2.me/theorems/bdce1035-4d75-40c1-83c8-7cad1219ce2f
-- title:
--   Stopped exponential-loss process and conditional Lundberg capital bound: srAdjustment
-- statement:
--   Positive adjustment exponent for exponential severities under loading. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[M_{\tau\wedge N}]\le1\ \Longrightarrow\ \psi_N(u)\le e^{-Ru}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def srAdjustment (lambda c beta : ℝ) : ℝ := beta-lambda/c

end ActuarialValuation


