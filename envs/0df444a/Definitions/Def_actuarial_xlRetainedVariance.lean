-- Prove2me | Definitions.Def_actuarial_xlRetainedVariance
-- name    : actuarial_xlRetainedVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:57:06.282019+00:00
-- url     : https://prove2.me/theorems/c1e4dd2b-319d-423f-820c-bb3ca1548550
-- title:
--   Variance of the retained claim under a finite scenario law
-- statement:
--   Finite weighted second central moment of the insurer's retained claim payment; nonnegative for nonnegative weights.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w[r(Z,a)]=\sum_\omega w_\omega(r(z_\omega,a)-\mathbb E[r])^2
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlExpectedLoss
import Definitions.Def_actuarial_xlRetainedLoss
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlRetainedVariance {Ω : Type*} [Fintype Ω]
  (w z : Ω → ℝ) (a : ℝ) : ℝ :=
  ∑ ω : Ω, w ω *
    (xlRetainedLoss (z ω) a -
      xlExpectedLoss w (fun x => xlRetainedLoss (z x) a)) ^ 2

end ActuarialValuation


