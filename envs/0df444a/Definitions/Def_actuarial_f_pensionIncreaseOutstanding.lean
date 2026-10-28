-- Prove2me | Definitions.Def_actuarial_f_pensionIncreaseOutstanding
-- name    : actuarial_f_pensionIncreaseOutstanding
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:49:36.71323+00:00
-- url     : https://prove2.me/theorems/0c1edadb-55d8-47eb-9b42-69fa86027079
-- title:
--   Unmet authorised ordinary pension increase
-- statement:
--   Deduct certified permitted earlier ordinary pension increase credit, never apply this generic credit automatically to section 109 GMP.
--
--   The defining expression is:
--
--   $$
--   u_{\mathrm{out}}=\max(0,u_{\mathrm{req}}-u_{\mathrm{credited}})
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def pensionIncreaseOutstanding
    (required credited : ℝ) : ℝ :=
  max 0 (required - credited)
end ActuarialUnderpinsF


