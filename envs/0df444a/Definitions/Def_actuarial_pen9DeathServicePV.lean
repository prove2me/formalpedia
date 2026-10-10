-- Prove2me | Definitions.Def_actuarial_pen9DeathServicePV
-- name    : actuarial_pen9DeathServicePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:44.567977+00:00
-- url     : https://prove2.me/theorems/0a0706c8-211b-4be1-9598-ec60a436a34d
-- title:
--   Service-table exits, survivor and deferred benefits: pen9DeathServicePV
-- statement:
--   Expected present value of salary-linked death-in-service survivor pension or equivalent capital, with the spouse annuity factor covering the stated death contingency. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PV_d=q^d S m a_{sp}v
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pen9DeathServicePV (death salary cover spouseAnnuity discount : ℝ) : ℝ := death*salary*cover*spouseAnnuity*discount

end ActuarialValuation


