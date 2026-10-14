-- Prove2me | Definitions.Def_actuarial_c_cont_deathSecondEPV
-- name    : actuarial_c_cont_deathSecondEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:00:55.416614+00:00
-- url     : https://prove2.me/theorems/e109ba3f-b625-4d31-a7f4-b78d60d1250f
-- title:
--   Expected square of the realised immediate-death cashflow under its actual lifetime measure.
-- statement:
--   Expected square of the realised immediate-death cashflow under its actual lifetime measure.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def deathSecondEPV (μ : Measure ℝ) (n delta : ℝ) : ℝ :=
  ∫ t, (deathPV n delta t)^2 ∂μ

end ActuarialAssurances.Continuous


