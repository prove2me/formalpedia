-- Prove2me | Definitions.Def_actuarial_c_cont_fractionalSettlementPV
-- name    : actuarial_c_cont_fractionalSettlementPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:00:43.015866+00:00
-- url     : https://prove2.me/theorems/df865a9c-6a9a-4bdb-82a0-51a7bd12292d
-- title:
--   A death in half-open m-thly period r is paid at the subsequent fractional anniversary.
-- statement:
--   A death in half-open m-thly period r is paid at the subsequent fractional anniversary.
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

noncomputable def fractionalSettlementPV (m h : ℕ) (delta t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m*h),
    if fractionalTime m r ≤ t ∧ t < fractionalTime m (r+1)
    then Real.exp (-delta * fractionalTime m (r+1)) else 0

end ActuarialAssurances.Continuous


