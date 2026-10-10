-- Prove2me | Definitions.Def_actuarial_pen9ActiveProbability
-- name    : actuarial_pen9ActiveProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:22.679001+00:00
-- url     : https://prove2.me/theorems/5576ed71-7443-46a6-9b35-3ba6a217eea5
-- title:
--   Service-table exits, survivor and deferred benefits: pen9ActiveProbability
-- statement:
--   Probability of remaining in active service under the complete set of exits. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p^a=1-\sum_kq^k
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitMass

namespace ActuarialValuation

noncomputable def pen9ActiveProbability (withdrawal death disability retirement : ℝ) : ℝ := 1-pen9ExitMass withdrawal death disability retirement

end ActuarialValuation


