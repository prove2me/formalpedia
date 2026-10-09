-- Prove2me | Definitions.Def_actuarial_finiteExponentialMoment
-- name    : actuarial_finiteExponentialMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:52:35.456312+00:00
-- url     : https://prove2.me/theorems/f4e9adb6-9b60-45c5-867c-1df2899bfc09
-- title:
--   Finite weighted moment-generating expression
-- statement:
--   The finite weighted exponential moment of a real loss at sensitivity gamma. For actuarial probability use nonnegative unit-total weights.
--
--   **Mathematical statement**
--
--   $$
--   M_\gamma(X)=\sum_\omega w_\omega e^{\gamma X_\omega}
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteExponentialMoment {Ω : Type*} [Fintype Ω]
  (w X : Ω → ℝ) (gamma : ℝ) : ℝ :=
  ∑ ω : Ω, w ω * Real.exp (gamma * X ω)

end ActuarialValuation


