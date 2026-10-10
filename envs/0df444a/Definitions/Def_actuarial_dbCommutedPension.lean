-- Prove2me | Definitions.Def_actuarial_dbCommutedPension
-- name    : actuarial_dbCommutedPension
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T19:22:59.667134+00:00
-- url     : https://prove2.me/theorems/f7cfb23d-c050-492f-ab2a-e0bb6215bdc4
-- title:
--   dbCommutedPension
-- statement:
--   Original derived definition for UK DB pension valuation. Commuting a pension of g annually at cash-per-pension factor f reduces the annual pension by L/f. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   P_B=g-L/f
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def dbCommutedPension (g L f : ℝ) : ℝ :=
  g - L / f

end ActuarialValuation


