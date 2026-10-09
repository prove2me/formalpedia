-- Prove2me | Definitions.Def_actuarial_finiteEntropicPremium
-- name    : actuarial_finiteEntropicPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:53:17.986944+00:00
-- url     : https://prove2.me/theorems/c6f653aa-0e6f-441d-9582-43e25d1b8c82
-- title:
--   Finite exponential certainty-equivalent premium
-- statement:
--   Exponential premium or entropic risk measure at nonzero sensitivity gamma, interpreted when the exponential moment is positive.
--
--   **Mathematical statement**
--
--   $$
--   \rho_\gamma(X)=\frac1\gamma\log\sum_\omega w_\omega e^{\gamma X_\omega}
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteEntropicPremium {Ω : Type*} [Fintype Ω]
  (w X : Ω → ℝ) (gamma : ℝ) : ℝ :=
  Real.log (finiteExponentialMoment w X gamma) / gamma

end ActuarialValuation


