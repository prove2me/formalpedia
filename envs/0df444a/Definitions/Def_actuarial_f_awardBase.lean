-- Prove2me | Definitions.Def_actuarial_f_awardBase
-- name    : actuarial_f_awardBase
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T22:11:25.305217+00:00
-- url     : https://prove2.me/theorems/f1cfa137-ec59-4778-b85b-825a72487ea0
-- title:
--   Award base
-- statement:
--   Award base models an irrevocably selected maximum at pension commencement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   U_z=\max(A_z,B_z)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def awardBase (a b : ℕ → ℝ) (z : ℕ) : ℝ :=
  max (a z) (b z)

-- The known award-date winner keeps its own subsequent increase stream.
end ActuarialUnderpinsF


