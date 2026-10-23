-- Prove2me | Definitions.Def_actuarial_f_spouseBaseAtDeath
-- name    : actuarial_f_spouseBaseAtDeath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T06:54:32.252409+00:00
-- url     : https://prove2.me/theorems/de205bda-d592-429d-a27d-67c764ecba20
-- title:
--   Spouse base at death
-- statement:
--   Spouse base at death models survivor pension entitlement determined at member death. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   S_{zi}=\max(S^{A}_{zi},S^{B}_{zi})
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def spouseBaseAtDeath (z i : ℕ)
    (spouseAlternativeOne spouseAlternativeTwo : ℕ → ℕ → ℝ) : ℝ :=
  max (spouseAlternativeOne z i) (spouseAlternativeTwo z i)
end ActuarialUnderpinsF


