-- Prove2me | Definitions.Def_actuarial_c_cont_recipientDeathPV
-- name    : actuarial_c_cont_recipientDeathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:00:18.665264+00:00
-- url     : https://prove2.me/theorems/bbabf94c-33ad-415d-a73e-220b8e6e5da9
-- title:
--   A time-dependent death-benefit entitlement multiplier; not yet a joint-life beneficiary model.
-- statement:
--   A time-dependent death-benefit entitlement multiplier; not yet a joint-life beneficiary model.
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

noncomputable def recipientDeathPV (n delta t : ℝ)
    (entitlement : ℝ → ℝ) : ℝ :=
  entitlement t * deathPV n delta t

end ActuarialAssurances.Continuous


