-- Prove2me | Definitions.Def_actuarial_quotaShareCededClaim
-- name    : actuarial_quotaShareCededClaim
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:59:28.091977+00:00
-- url     : https://prove2.me/theorems/2c6b772d-1625-4451-9dab-d2ffbe078b71
-- title:
--   Reinsurer's complementary share of the claim
-- statement:
--   The amount ceded to the reinsurer is the complementary proportion of the claim. Together with the retained share it must reproduce the entire policyholder payment for every claim scenario, so there is no double counting of benefit cashflows.
--
--   **Mathematical statement**
--
--   $$
--   C_r(X)=(1-r)X
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def quotaShareCededClaim (claim retention : ℝ) : ℝ :=
  (1 - retention) * claim

end ActuarialValuation


