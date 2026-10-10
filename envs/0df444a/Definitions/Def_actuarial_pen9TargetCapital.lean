-- Prove2me | Definitions.Def_actuarial_pen9TargetCapital
-- name    : actuarial_pen9TargetCapital
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:52.650701+00:00
-- url     : https://prove2.me/theorems/0a961901-06d6-46f9-bd8a-50708a1b34b7
-- title:
--   DC accumulation and replacement-ratio annuity funding: pen9TargetCapital
-- statement:
--   Target capital for a specified salary-replacement percentage of pension income, priced on a stated annuity basis. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   K=\tau S_R a^*
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pen9TargetCapital (retirementSalary ratio annuity : ℝ) : ℝ := ratio*retirementSalary*annuity

end ActuarialValuation


