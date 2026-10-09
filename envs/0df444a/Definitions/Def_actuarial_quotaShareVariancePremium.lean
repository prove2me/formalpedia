-- Prove2me | Definitions.Def_actuarial_quotaShareVariancePremium
-- name    : actuarial_quotaShareVariancePremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:00:15.57649+00:00
-- url     : https://prove2.me/theorems/ec30a2c5-aeb2-4576-b72f-b0e244c38e97
-- title:
--   Premium combining expected ceded loss and variance loading
-- statement:
--   The insurer pays the reinsurer the expected ceded amount for a Bernoulli claim of fixed amount claim and probability q, plus a loading on the variance of that ceded Bernoulli amount. The loading parameter has the inverse currency units required by a variance-premium formula.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_r=q(1-r)b+\lambda q(1-q)(1-r)^2b^2
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCededClaim

namespace ActuarialValuation

noncomputable def quotaShareVariancePremium
  (q claim retention loading : ℝ) : ℝ :=
  q * quotaShareCededClaim claim retention +
    loading * q * (1 - q) *
      (quotaShareCededClaim claim retention) ^ 2

end ActuarialValuation


