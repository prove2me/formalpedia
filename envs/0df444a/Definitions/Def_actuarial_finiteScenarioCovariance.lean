-- Prove2me | Definitions.Def_actuarial_finiteScenarioCovariance
-- name    : actuarial_finiteScenarioCovariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:20:01.037284+00:00
-- url     : https://prove2.me/theorems/6ae87309-b0b1-4f35-9011-6e290adb75e4
-- title:
--   Covariance of two finite scenario cashflows
-- statement:
--   Finite weighted covariance, zero when the two centred annual cashflows are orthogonal.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Cov}_w(X,Y)=\sum_\omega w_\omega(X_\omega-\mathbb E[X])(Y_\omega-\mathbb E[Y])
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteScenarioCovariance {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (X Y : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, w ω *
   (X ω - finiteScenarioExpectation w X) *
   (Y ω - finiteScenarioExpectation w Y)

end ActuarialValuation


