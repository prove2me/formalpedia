-- Prove2me | Definitions.Def_actuarial_xlExpectedValuePremiumCost
-- name    : actuarial_xlExpectedValuePremiumCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:56:39.678978+00:00
-- url     : https://prove2.me/theorems/02289f63-42c8-4a79-a95a-7e5690ccf49b
-- title:
--   Expected retained losses plus loaded ceded loss premium
-- statement:
--   Total expected one-period insurer cost under an expected-value reinsurance premium with loading theta.
--
--   **Mathematical statement**
--
--   $$
--   C_\theta(a)=\mathbb E[r(Z,a)]+(1+\theta)\mathbb E[c(Z,a)]
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlExpectedValuePremiumCost {Ω : Type*} [Fintype Ω]
  (w z : Ω → ℝ) (a θ : ℝ) : ℝ :=
  xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) a) +
    (1 + θ) * xlExpectedLoss w (fun ω => xlCededLoss (z ω) a)

end ActuarialValuation


