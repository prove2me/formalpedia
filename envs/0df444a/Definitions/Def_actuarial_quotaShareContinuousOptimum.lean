-- Prove2me | Definitions.Def_actuarial_quotaShareContinuousOptimum
-- name    : actuarial_quotaShareContinuousOptimum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:01:15.668327+00:00
-- url     : https://prove2.me/theorems/40185133-f017-4fe5-bf9b-234c056ab4da
-- title:
--   Candidate optimal retention under two variance coefficients
-- statement:
--   The candidate is the ceded-variance premium loading divided by the sum of the ceded-variance loading and retained-variance capital charge. Both coefficients must be nonnegative with positive total to place the optimum in the allowed quota-share interval.
--
--   **Mathematical statement**
--
--   $$
--   r^*=\lambda/(\lambda+\alpha)
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def quotaShareContinuousOptimum
  (loading capital : ℝ) : ℝ := loading / (loading + capital)

end ActuarialValuation


