-- Prove2me | Definitions.Def_actuarial_f_gmpCertifiedMemberPayable
-- name    : actuarial_f_gmpCertifiedMemberPayable
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:49:30.953408+00:00
-- url     : https://prove2.me/theorems/548aebef-cfed-4c12-883c-aacf67931598
-- title:
--   Contractual member pension subject to certified minimum
-- statement:
--   Represent legally certified payable pension as the larger of scheme benefit and certified statutory floor. The floor is external and must be validated.
--
--   The defining expression is:
--
--   $$
--   P_t=\max(C_t,M_t^{\mathrm{certified}})
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpCertifiedMemberPayable
    (contractual certifiedStatutoryFloor : ℝ) : ℝ :=
  max contractual certifiedStatutoryFloor
end ActuarialUnderpinsF


