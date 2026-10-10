-- Prove2me | Definitions.Def_actuarial_pen9DCFund
-- name    : actuarial_pen9DCFund
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:38.258094+00:00
-- url     : https://prove2.me/theorems/a2ee1f90-5ebe-45ff-8dd9-f95daae4e164
-- title:
--   DC accumulation and replacement-ratio annuity funding: pen9DCFund
-- statement:
--   DC fund accumulated from a fixed salary-proportional contribution rate, paid in arrears. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A_n=cF_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AccumFactor

namespace ActuarialValuation

noncomputable def pen9DCFund (rate : ℝ) (salary : ℕ → ℝ) (investment : ℝ) (years : ℕ) : ℝ := rate * pen9AccumFactor salary investment years

end ActuarialValuation


