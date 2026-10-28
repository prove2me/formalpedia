-- Prove2me | Definitions.Def_actuarial_f_linkedFirstTranche
-- name    : actuarial_f_linkedFirstTranche
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:39:19.797443+00:00
-- url     : https://prove2.me/theorems/03e93257-da46-4324-aa1e-1897b9549a80
-- title:
--   First tranche keeps selected increase path
-- statement:
--   The elected member pension retains the increase path belonging to the selected option and is paid only when the member instalment is due.
--
--   The defining relationship is:
--
--   $$
--   C^{(1)}_t=\mathbf1_{\mathrm{due}}P^{\mathrm{choice}}_t
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_fixedChoicePayment

namespace ActuarialUnderpinsF
noncomputable def linkedFirstTranche (r z i t : ℕ)
    (a b ga gb : ℕ → ℝ) : ℝ :=
  fixedChoicePayment a b ga gb z t * memberDue r i t
end ActuarialUnderpinsF


