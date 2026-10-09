-- Prove2me | Definitions.Def_actuarial_finiteEntropicRetentionCost
-- name    : actuarial_finiteEntropicRetentionCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:24.738878+00:00
-- url     : https://prove2.me/theorems/e351cd25-26ca-4d63-bbb5-e9ab07b6eab5
-- title:
--   Reinsurance premium plus entropic risk of retained claims
-- statement:
--   Premium quoted by reinsurer at retention a plus the insurer's entropic valuation of claims still retained.
--
--   **Mathematical statement**
--
--   $$
--   J_\gamma(a)=q(a)+\rho_\gamma(\min(Z,a))
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
import Definitions.Def_actuarial_finiteEntropicRetainedClaim
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteEntropicRetentionCost {Ω : Type*} [Fintype Ω]
  (w z : Ω → ℝ) (reinsurancePremium : ℝ → ℝ)
  (gamma a : ℝ) : ℝ :=
  reinsurancePremium a +
    finiteEntropicPremium w (fun ω => finiteEntropicRetainedClaim (z ω) a) gamma

end ActuarialValuation


