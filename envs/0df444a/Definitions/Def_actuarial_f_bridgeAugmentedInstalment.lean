-- Prove2me | Definitions.Def_actuarial_f_bridgeAugmentedInstalment
-- name    : actuarial_f_bridgeAugmentedInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:37:03.198864+00:00
-- url     : https://prove2.me/theorems/504bd7f3-5a2d-453d-b172-ca48b49a7703
-- title:
--   Bridge augmented instalment
-- statement:
--   Bridge augmented instalment models an extra temporary pension stopping at the specified cessation anniversary. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{\text{bridge}}_t=C_t+B\mathbf1_{\{u\le t<v\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeInstalment
import Definitions.Def_actuarial_f_totalInstalment

namespace ActuarialUnderpinsF
noncomputable def bridgeAugmentedInstalment (h r g z i j t : ℕ)
    (start stop : ℕ) (bridge : ℝ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) : ℝ :=
  totalInstalment h r g z i j t a b c s estate g0 g1 gs ge +
    bridgeInstalment start stop t bridge
end ActuarialUnderpinsF


