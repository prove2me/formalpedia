-- Prove2me | Definitions.Def_actuarial_finiteScenarioExpectation
-- name    : actuarial_finiteScenarioExpectation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:15:50.316466+00:00
-- url     : https://prove2.me/theorems/867b3ff6-0dfc-4db0-9eec-8058f038e45a
-- title:
--   Weighted expected value on finitely many outcomes
-- statement:
--   Finite-scenario expectation, with nonnegative weights and unit sum required for probabilistic interpretation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[X]=\sum_{\omega}w_\omega X_\omega
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteScenarioExpectation {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, w ω * X ω

end ActuarialValuation


