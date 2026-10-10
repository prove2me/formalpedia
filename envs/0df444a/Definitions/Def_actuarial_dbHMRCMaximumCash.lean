-- Prove2me | Definitions.Def_actuarial_dbHMRCMaximumCash
-- name    : actuarial_dbHMRCMaximumCash
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:23:06.072847+00:00
-- url     : https://prove2.me/theorems/ef1c1ebc-6325-4d44-973c-d9b657674ab6
-- title:
--   dbHMRCMaximumCash
-- statement:
--   Original derived definition for UK DB pension valuation. In the simple single-DB-entitlement no-credit, no-other-lump-sum case, the statutory applicable amount bounds the pension commencement cash. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   L_{\max}=20fg/(20+3f)
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def dbHMRCMaximumCash (g f : ℝ) : ℝ :=
  20 * f * g / (20 + 3 * f)

end ActuarialValuation


