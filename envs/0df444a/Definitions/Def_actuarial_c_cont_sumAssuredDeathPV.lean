-- Prove2me | Definitions.Def_actuarial_c_cont_sumAssuredDeathPV
-- name    : actuarial_c_cont_sumAssuredDeathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:59:34.182808+00:00
-- url     : https://prove2.me/theorems/83f3cd66-d895-466d-8925-a5a983a63687
-- title:
--   A fixed death lump sum multiplies the unit immediate death claim.
-- statement:
--   A fixed death lump sum multiplies the unit immediate death claim.
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

noncomputable def sumAssuredDeathPV (n delta sumAssured t : ℝ) : ℝ :=
  sumAssured * deathPV n delta t

end ActuarialAssurances.Continuous


