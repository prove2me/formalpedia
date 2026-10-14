-- Prove2me | Definitions.Def_actuarial_c_cont_fractionalTime
-- name    : actuarial_c_cont_fractionalTime
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:59:44.833991+00:00
-- url     : https://prove2.me/theorems/c8db075e-1b6f-4acf-a9df-111ff75665dc
-- title:
--   The policy payment instant represented by integer index r on an m-thly time grid.
-- statement:
--   The policy payment instant represented by integer index r on an m-thly time grid.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def fractionalTime (m r : ℕ) : ℝ := (r : ℝ) / (m : ℝ)

end ActuarialAssurances.Continuous


