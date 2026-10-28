-- Prove2me | Definitions.Def_actuarial_f_completeMonths
-- name    : actuarial_f_completeMonths
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:37:33.828901+00:00
-- url     : https://prove2.me/theorems/4fbeb12f-cd60-4608-8196-89e64d1aaa30
-- title:
--   Complete months to first increase
-- statement:
--   Count complete calendar months since retirement, capped at twelve.
--
--   The defining relationship is:
--
--   $$
--   m=\min(12,D_1-R)
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def completeMonths (retirement first : ℕ) : ℕ :=
  min 12 (first - retirement)
end ActuarialUnderpinsF


