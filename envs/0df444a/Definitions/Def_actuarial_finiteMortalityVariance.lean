-- Prove2me | Definitions.Def_actuarial_finiteMortalityVariance
-- name    : actuarial_finiteMortalityVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:07:14.542649+00:00
-- url     : https://prove2.me/theorems/11272833-7d9f-40f8-ae79-c9b39ea262fe
-- title:
--   Finite-scenario variance about weighted mean
-- statement:
--   Weighted sum of squared deviations from the same finite-scenario weighted mean, with probabilistic interpretation for unit-sum nonnegative weights.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(X)=\sum_\omega w_\omega(X_\omega-\sum_a w_aX_a)^2
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalityVariance {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, w ω * (X ω - (∑ a : Ω, w a * X a)) ^ 2

end ActuarialValuation


