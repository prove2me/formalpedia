-- Prove2me | Definitions.Def_actuarial_c_cont_deathEPV
-- name    : actuarial_c_cont_deathEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:58:32.838986+00:00
-- url     : https://prove2.me/theorems/f53331d7-0b25-4f71-bc7e-d8697954daec
-- title:
--   Expectation of the immediate-death claim under an actual probability law on real lifetimes.
-- statement:
--   Expectation of the immediate-death claim under an actual probability law on real lifetimes.
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

noncomputable def deathEPV (μ : Measure ℝ) (n delta : ℝ) : ℝ :=
  ∫ t, deathPV n delta t ∂μ

end ActuarialAssurances.Continuous


