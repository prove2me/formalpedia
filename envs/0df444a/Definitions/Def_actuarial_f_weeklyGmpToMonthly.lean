-- Prove2me | Definitions.Def_actuarial_f_weeklyGmpToMonthly
-- name    : actuarial_f_weeklyGmpToMonthly
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:49:43.704899+00:00
-- url     : https://prove2.me/theorems/cb3dc8f6-edc7-49e3-9805-c5dd39c55ac9
-- title:
--   Convert statutory weekly GMP to monthly instalment units
-- statement:
--   Convert weekly GMP using 52/12 before applying the per-monthly-instalment valuation contract. Rounding is a separate scheme-rule step.
--
--   The defining expression is:
--
--   $$
--   G_{\mathrm{month}}=G_{\mathrm{week}}\times52/12
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def weeklyGmpToMonthly (gmpWeekly : ℝ) : ℝ :=
  gmpWeekly * 52 / 12
end ActuarialUnderpinsF


