-- Prove2me | Definitions.Def_actuarial_f_memberDue
-- name    : actuarial_f_memberDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T12:55:56.877588+00:00
-- url     : https://prove2.me/theorems/ff52874e-b7f2-410d-bfcf-0a04afb0dbf9
-- title:
--   Member due
-- statement:
--   Member due models member pension instalments payable only while alive after commencement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   m_i(t)=\mathbf1_{\{r\le t\le i\}}
--   $$
--
--   The formal definition delegates its two-life kernel to the published CII module, with F-specific award-state, retirement and censoring conditions retained.
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page. Reuses CII published actuarial_d_alive; additionally restricted to dates on or after retirement. External import must be verified in the exact pinned environment.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Definitions.Def_actuarial_d_alive

namespace ActuarialUnderpinsF
noncomputable def memberDue (r i t : ℕ) : ℝ :=
  if r ≤ t then ActuarialJointD.alive i t else 0
end ActuarialUnderpinsF


