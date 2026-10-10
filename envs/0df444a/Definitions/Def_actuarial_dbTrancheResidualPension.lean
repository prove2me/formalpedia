-- Prove2me | Definitions.Def_actuarial_dbTrancheResidualPension
-- name    : actuarial_dbTrancheResidualPension
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:25:40.962482+00:00
-- url     : https://prove2.me/theorems/80265d9e-a088-4186-9753-efeda383ee1b
-- title:
--   dbTrancheResidualPension
-- statement:
--   Original derived definition for UK DB pension valuation. After allocating commutation separately by tranche, total annual pension is the sum of each retained tranche. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   P_B=\sum_{i<n}(p_i-x_i)
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def dbTrancheResidualPension (pension reduction : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (pension i - reduction i)

end ActuarialValuation


