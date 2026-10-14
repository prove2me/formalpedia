-- Prove2me | Definitions.Def_actuarial_c_cont_deathPV
-- name    : actuarial_c_cont_deathPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:57:39.638723+00:00
-- url     : https://prove2.me/theorems/ded8cc7f-f61d-4ba5-99c7-aac3fbaf2681
-- title:
--   Unit insurance proceeds are payable at the actual death instant only if death occurs before maturity.
-- statement:
--   Unit insurance proceeds are payable at the actual death instant only if death occurs before maturity.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def deathPV (n delta t : ℝ) : ℝ :=
  if 0 ≤ t ∧ t < n then Real.exp (-delta * t) else 0

end ActuarialAssurances.Continuous


