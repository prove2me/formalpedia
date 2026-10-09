-- Prove2me | Definitions.Def_actuarial_quotaShareRetainedClaim
-- name    : actuarial_quotaShareRetainedClaim
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:59:13.049944+00:00
-- url     : https://prove2.me/theorems/da915301-7e39-49d6-b531-ff85b06417db
-- title:
--   Insurer's retained share of a nonnegative claim
-- statement:
--   The insurer pays proportion retention of the original claim. The definition is algebraic over all real fractions, while physically admissible reinsurance contracts require retention between zero and one and claim amounts that are nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   R_r(X)=rX
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def quotaShareRetainedClaim (claim retention : ℝ) : ℝ :=
  retention * claim

end ActuarialValuation


