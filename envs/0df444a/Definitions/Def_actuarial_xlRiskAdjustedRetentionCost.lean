-- Prove2me | Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
-- name    : actuarial_xlRiskAdjustedRetentionCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:57:47.817989+00:00
-- url     : https://prove2.me/theorems/cb30a4d2-38c4-4161-8c63-d07abe9717fb
-- title:
--   Expected-value reinsurance cost plus retained-loss variance charge
-- statement:
--   A deliberately simple illustrative cost-of-capital proxy charging lambda per unit of retained-claim variance in addition to expected reinsurance cost.
--
--   **Mathematical statement**
--
--   $$
--   J_{\theta,\lambda}(a)=C_\theta(a)+\lambda\operatorname{Var}_w[r(Z,a)]
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
import Definitions.Def_actuarial_xlRetainedVariance
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlRiskAdjustedRetentionCost {Ω : Type*} [Fintype Ω]
  (w z : Ω → ℝ) (θ kap a : ℝ) : ℝ :=
  xlExpectedValuePremiumCost w z a θ + kap * xlRetainedVariance w z a

end ActuarialValuation


