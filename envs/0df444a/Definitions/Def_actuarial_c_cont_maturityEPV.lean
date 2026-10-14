-- Prove2me | Definitions.Def_actuarial_c_cont_maturityEPV
-- name    : actuarial_c_cont_maturityEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:58:45.815991+00:00
-- url     : https://prove2.me/theorems/525a962f-3e34-4257-a6a7-3fe516779dba
-- title:
--   Expectation of the maturity benefit, including an atom exactly at maturity.
-- statement:
--   Expectation of the maturity benefit, including an atom exactly at maturity.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_maturityPV

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def maturityEPV (μ : Measure ℝ) (n delta : ℝ) : ℝ :=
  ∫ t, maturityPV n delta t ∂μ

end ActuarialAssurances.Continuous


