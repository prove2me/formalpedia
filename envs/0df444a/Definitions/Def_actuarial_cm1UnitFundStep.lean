-- Prove2me | Definitions.Def_actuarial_cm1UnitFundStep
-- name    : actuarial_cm1UnitFundStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:52:58.917343+00:00
-- url     : https://prove2.me/theorems/d6984d19-5af6-40dd-a3f5-bb7df033b77f
-- title:
--   Projected profits and unit-linked funds: cm1UnitFundStep
-- statement:
--   A unit-linked investment account projection following premium allocation, fund charge and investment return. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{t+1}=(U_t+P_{\rm alloc}-C_f)(1+j)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1UnitFundStep (opening allocatedPremium fundCharge returnRate : ℝ) : ℝ :=
  (opening + allocatedPremium - fundCharge) * (1 + returnRate)

end ActuarialValuation


