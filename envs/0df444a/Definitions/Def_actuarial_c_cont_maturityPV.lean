-- Prove2me | Definitions.Def_actuarial_c_cont_maturityPV
-- name    : actuarial_c_cont_maturityPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:57:50.077804+00:00
-- url     : https://prove2.me/theorems/d8855e3a-ae54-4219-97a4-26acaf34e854
-- title:
--   The pure-endowment unit is payable at the fixed maturity instant for death at or after that instant.
-- statement:
--   The pure-endowment unit is payable at the fixed maturity instant for death at or after that instant.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def maturityPV (n delta t : ℝ) : ℝ :=
  if n ≤ t then Real.exp (-delta * n) else 0

end ActuarialAssurances.Continuous


