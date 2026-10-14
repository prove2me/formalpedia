-- Prove2me | Definitions.Def_actuarial_c_cont_annualSettlementPV
-- name    : actuarial_c_cont_annualSettlementPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:00:29.611957+00:00
-- url     : https://prove2.me/theorems/2b9f6252-3b10-4b3c-8123-8c95623453af
-- title:
--   A death in half-open year j is paid at the subsequent integer policy anniversary.
-- statement:
--   A death in half-open year j is paid at the subsequent integer policy anniversary.
--
--   Conventions: T is a realised lifetime. Where a probability distribution is used, it must be specified as a Measure ℝ and not inferred from annual life-table values.
-- source:
--   Original formal cashflow encoding informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 8; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c08.xhtml. The displayed Lean declaration is an independently formulated definition, not a quotation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAssurances.Continuous

open MeasureTheory

noncomputable def annualSettlementPV (h : ℕ) (delta t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range h,
    if (j : ℝ) ≤ t ∧ t < ((j+1 : ℕ) : ℝ)
    then Real.exp (-delta * ((j+1 : ℕ) : ℝ)) else 0

end ActuarialAssurances.Continuous


