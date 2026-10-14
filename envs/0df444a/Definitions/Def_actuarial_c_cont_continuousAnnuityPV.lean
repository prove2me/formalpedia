-- Prove2me | Definitions.Def_actuarial_c_cont_continuousAnnuityPV
-- name    : actuarial_c_cont_continuousAnnuityPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:58:09.328988+00:00
-- url     : https://prove2.me/theorems/6cabd995-39ce-4072-819b-ec696c5cb26a
-- title:
--   The realised continuously paid annuity is the integrated discount kernel, with a separate zero-force branch.
-- statement:
--   The realised continuously paid annuity is the integrated discount kernel, with a separate zero-force branch.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def continuousAnnuityPV (n delta t : ℝ) : ℝ :=
  if delta = 0 then exposure n t
  else (1 - Real.exp (-delta * exposure n t)) / delta

end ActuarialAssurances.Continuous


