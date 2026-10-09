-- Prove2me | Definitions.Def_actuarial_finiteScenarioVariance
-- name    : actuarial_finiteScenarioVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:18:55.722806+00:00
-- url     : https://prove2.me/theorems/036791a9-193c-4b48-ac09-5a0d6c1da24d
-- title:
--   Variance of a finite scenario payoff
-- statement:
--   Sum of weighted squared deviations from the scenario expectation.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(X)=\sum_\omega w_\omega(X_\omega-\mathbb E_w[X])^2
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteScenarioVariance {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, w ω *
    (X ω - finiteScenarioExpectation w X) ^ 2

end ActuarialValuation


