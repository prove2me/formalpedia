-- Prove2me | Definitions.Def_actuarial_c_cont_exposure
-- name    : actuarial_c_cont_exposure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:57:30.089985+00:00
-- url     : https://prove2.me/theorems/dedb7836-9020-48f1-b620-0a8c6945d68e
-- title:
--   Death or maturity ends continuous premium/annuity exposure at the earlier of the actual death instant and maturity.
-- statement:
--   Death or maturity ends continuous premium/annuity exposure at the earlier of the actual death instant and maturity.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def exposure (n t : ℝ) : ℝ := min n (max 0 t)

end ActuarialAssurances.Continuous


