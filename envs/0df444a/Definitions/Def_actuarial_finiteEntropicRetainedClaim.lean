-- Prove2me | Definitions.Def_actuarial_finiteEntropicRetainedClaim
-- name    : actuarial_finiteEntropicRetainedClaim
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:53:34.426035+00:00
-- url     : https://prove2.me/theorems/3debb644-4f94-41df-909d-c00958435f85
-- title:
--   Insurer claim retained under a fixed excess-of-loss limit
-- statement:
--   The smaller of gross realised claim and the cedant retention threshold, without probabilities.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)=\min(z,a)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteEntropicRetainedClaim
  (z a : ℝ) : ℝ := min z a

end ActuarialValuation


