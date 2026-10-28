-- Prove2me | Definitions.Def_actuarial_f_gmpDaysInMonth
-- name    : actuarial_f_gmpDaysInMonth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:46:04.221249+00:00
-- url     : https://prove2.me/theorems/789b7caa-3db2-4623-8821-4d33644cab5e
-- title:
--   Length of a Gregorian calendar month
-- statement:
--   Return 28 or 29 days for February and 30 or 31 for other valid months; invalid months have zero days.
--
--   The defining expression is:
--
--   $$
--   d(y,m)\in\{0,28,29,30,31\}
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpLeapYear

namespace ActuarialUnderpinsF
noncomputable def gmpDaysInMonth (year month : ℕ) : ℕ := by
  classical
  exact if month = 2 then (if gmpLeapYear year then 29 else 28)
    else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30
    else if 1 ≤ month ∧ month ≤ 12 then 31 else 0
end ActuarialUnderpinsF


