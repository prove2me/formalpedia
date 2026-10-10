-- Prove2me | Definitions.Def_actuarial_pen9AverageSalary
-- name    : actuarial_pen9AverageSalary
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:02.184932+00:00
-- url     : https://prove2.me/theorems/61e63bc5-5e4e-47a2-9b43-03acb7cb393a
-- title:
--   Salary scales, average pay and fractional service: pen9AverageSalary
-- statement:
--   Arithmetic average of pensionable salary over a finite, contiguous period starting at year first. A zero-year window returns zero by field division. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \bar S=(1/k)\sum_{t=0}^{k-1}S_{a+t}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pen9AverageSalary (salary : ℕ → ℝ) (first years : ℕ) : ℝ := (∑ t ∈ Finset.range years, salary (first+t)) / (years:ℝ)

end ActuarialValuation


