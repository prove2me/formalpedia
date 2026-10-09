-- Prove2me | Definitions.Def_actuarial_quotaShareCapitalObjective
-- name    : actuarial_quotaShareCapitalObjective
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:00:59.991987+00:00
-- url     : https://prove2.me/theorems/c3431766-e27c-4c99-a43e-b36230bd2f51
-- title:
--   Expected cost plus quadratic retained-risk capital
-- statement:
--   The insurer objective adds expected retained claims, the actual reinsurance premium and a penalty proportional to retained claim variance. This treats annual premium expense as deterministic once the treaty is chosen and does not mistakenly include reinsurance-premium variability in the residual loss.
--
--   **Mathematical statement**
--
--   $$
--   J(r)=qr b+\Pi_r+\alpha q(1-q)r^2b^2
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareRetainedClaim
import Definitions.Def_actuarial_quotaShareVariancePremium

namespace ActuarialValuation

noncomputable def quotaShareCapitalObjective
  (q claim retention loading capital : ℝ) : ℝ :=
  q * quotaShareRetainedClaim claim retention +
    quotaShareVariancePremium q claim retention loading +
    capital * q * (1 - q) *
      (quotaShareRetainedClaim claim retention) ^ 2

end ActuarialValuation


