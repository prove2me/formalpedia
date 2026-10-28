-- Prove2me | Definitions.Def_actuarial_f_afSurvivorSection87Eligible
-- name    : actuarial_f_afSurvivorSection87Eligible
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T13:02:10.771891+00:00
-- url     : https://prove2.me/theorems/3427bbb2-8f64-4884-896c-b6d274f5b676
-- title:
--   Section 87(2) survivor applicability
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def afSurvivorSection87Eligible
    (cessation memberDeath gmpCommencement payment : ℕ)
    (leftBefore1985 contractedOutEndedBefore1985
       fullSurvivorEntitled completeSubstitute : Bool)
    (survivorRelevantSum survivorGmpCurrent memberGmpAtCessation
       excludedTransferGrowth : ℝ) : Prop :=
  cessation < min memberDeath gmpCommencement ∧ memberDeath < payment ∧
    leftBefore1985 = false ∧
    contractedOutEndedBefore1985 = false ∧ fullSurvivorEntitled = true ∧
    completeSubstitute = false ∧
    memberGmpAtCessation / 2 < survivorRelevantSum ∧
    memberGmpAtCessation / 2 + excludedTransferGrowth < survivorGmpCurrent
end ActuarialUnderpinsF


