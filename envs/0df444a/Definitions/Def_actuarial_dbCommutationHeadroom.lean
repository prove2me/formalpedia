-- Prove2me | Definitions.Def_actuarial_dbCommutationHeadroom
-- name    : actuarial_dbCommutationHeadroom
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:23:20.316655+00:00
-- url     : https://prove2.me/theorems/e3e32afd-f431-4c5c-995a-199146d95943
-- title:
--   dbCommutationHeadroom
-- statement:
--   Original derived definition for UK DB pension valuation. The HMRC basic limit is expressed as a financial headroom that must remain nonnegative. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   H=20P_B-3L
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutedPension

namespace ActuarialValuation

noncomputable def dbCommutationHeadroom (g L f : ℝ) : ℝ :=
  20 * dbCommutedPension g L f - 3 * L

end ActuarialValuation


