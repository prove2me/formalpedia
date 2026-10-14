-- Prove2me | Definitions.Def_actuarial_c_cont_laggedDeathPV
-- name    : actuarial_c_cont_laggedDeathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:59:18.662618+00:00
-- url     : https://prove2.me/theorems/11ba5617-2081-4474-a37b-ba015c116346
-- title:
--   Settlement at the death instant plus a contractual real-valued payment lag.
-- statement:
--   Settlement at the death instant plus a contractual real-valued payment lag.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def laggedDeathPV (n delta lag t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t < n then Real.exp (-delta * (t + lag)) else 0

end ActuarialAssurances.Continuous


