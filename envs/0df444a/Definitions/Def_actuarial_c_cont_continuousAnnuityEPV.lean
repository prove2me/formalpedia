-- Prove2me | Definitions.Def_actuarial_c_cont_continuousAnnuityEPV
-- name    : actuarial_c_cont_continuousAnnuityEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:59:11.204977+00:00
-- url     : https://prove2.me/theorems/06a02efa-35dc-4b18-8996-76b00ecdb2de
-- title:
--   Expected continuously paid annuity under the same future-lifetime law as both terminal claims.
-- statement:
--   Expected continuously paid annuity under the same future-lifetime law as both terminal claims.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def continuousAnnuityEPV (μ : Measure ℝ) (n delta : ℝ) : ℝ :=
  ∫ t, continuousAnnuityPV n delta t ∂μ

end ActuarialAssurances.Continuous


