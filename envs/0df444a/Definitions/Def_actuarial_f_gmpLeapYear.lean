-- Prove2me | Definitions.Def_actuarial_f_gmpLeapYear
-- name    : actuarial_f_gmpLeapYear
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:45:53.011998+00:00
-- url     : https://prove2.me/theorems/b5823e73-3b1b-4d1e-882c-9ca195c3a71d
-- title:
--   Gregorian leap-year predicate
-- statement:
--   Recognise the 400-year exception and four-year recurrence used in valid YYYYMMDD dates.
--
--   The defining expression is:
--
--   $$
--   y\bmod400=0\vee(y\bmod4=0\wedge y\bmod100\ne0)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def gmpLeapYear (year : ℕ) : Prop :=
  year % 400 = 0 ∨ (year % 4 = 0 ∧ year % 100 ≠ 0)
end ActuarialUnderpinsF


