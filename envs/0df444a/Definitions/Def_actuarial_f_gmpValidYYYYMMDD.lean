-- Prove2me | Definitions.Def_actuarial_f_gmpValidYYYYMMDD
-- name    : actuarial_f_gmpValidYYYYMMDD
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:46:15.346883+00:00
-- url     : https://prove2.me/theorems/eb293062-c34c-4f96-9aeb-d5656ec61a79
-- title:
--   Valid Gregorian YYYYMMDD date
-- statement:
--   Ensure positive year, month in 1 to 12 and valid day of month including leap years.
--
--   The defining expression is:
--
--   $$
--   1\le m\le12,\;1\le d\le d(y,m)
--   $$
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpDaysInMonth

namespace ActuarialUnderpinsF
noncomputable def gmpValidYYYYMMDD (date : ℕ) : Prop :=
  let year := date / 10000
  let month := date % 10000 / 100
  let day := date % 100
  1 ≤ year ∧ 1 ≤ month ∧ month ≤ 12 ∧
    1 ≤ day ∧ day ≤ gmpDaysInMonth year month
end ActuarialUnderpinsF


