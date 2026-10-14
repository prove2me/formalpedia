-- Prove2me | Definitions.Def_actuarial_c_cont_fractionalDuePV
-- name    : actuarial_c_cont_fractionalDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:00:03.975992+00:00
-- url     : https://prove2.me/theorems/5c42467d-a6b8-4ce6-8e91-55639f17b70f
-- title:
--   An m-thly due annuity pays 1/m at each qualifying instant strictly before death.
-- statement:
--   An m-thly due annuity pays 1/m at each qualifying instant strictly before death.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def fractionalDuePV (m n : ℕ) (delta t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m*n),
    if fractionalTime m r < t then (1 / (m : ℝ)) *
      Real.exp (-delta * fractionalTime m r) else 0

end ActuarialAssurances.Continuous


