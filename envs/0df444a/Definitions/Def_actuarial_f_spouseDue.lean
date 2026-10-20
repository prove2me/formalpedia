-- Prove2me | Definitions.Def_actuarial_f_spouseDue
-- name    : actuarial_f_spouseDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T12:56:06.914463+00:00
-- url     : https://prove2.me/theorems/dac1efee-33eb-46ec-9421-0c690a352d4c
-- title:
--   Spouse due
-- statement:
--   Spouse due models survivor pension entitlement determined at member death. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   s_{ij}(t)=\mathbf1_{\{i<H,\ i<t\le j\}}
--   $$
--
--   The formal definition delegates its two-life kernel to the published CII module, with F-specific award-state, retirement and censoring conditions retained.
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page. Reuses CII published actuarial_d_onlyY, plus the contract's explicit censored-member exclusion. External import must be verified in the exact pinned environment.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Definitions.Def_actuarial_d_onlyY

namespace ActuarialUnderpinsF
noncomputable def spouseDue (h i j t : ℕ) : ℝ :=
  if i < h then ActuarialJointD.onlyY i j t else 0
end ActuarialUnderpinsF


