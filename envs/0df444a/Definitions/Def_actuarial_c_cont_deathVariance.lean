-- Prove2me | Definitions.Def_actuarial_c_cont_deathVariance
-- name    : actuarial_c_cont_deathVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:01:18.030907+00:00
-- url     : https://prove2.me/theorems/dd2ed948-4fff-42bc-8cea-07ca209b0278
-- title:
--   Second moment minus squared expected present value of the death cashflow.
-- statement:
--   Second moment minus squared expected present value of the death cashflow.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_deathSecondEPV

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def deathVariance (μ : Measure ℝ) (n delta : ℝ) : ℝ :=
  deathSecondEPV μ n delta - (deathEPV μ n delta)^2

end ActuarialAssurances.Continuous


