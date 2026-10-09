-- Prove2me | Definitions.Def_actuarial_xlExpectedLoss
-- name    : actuarial_xlExpectedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:55:04.196412+00:00
-- url     : https://prove2.me/theorems/d4cf1a3c-19f3-4a6d-90cd-6c6b2e6403eb
-- title:
--   Finite weighted expected claim
-- statement:
--   The real weighted expectation of a finite scenario claim amount; nonnegative unit-sum weights give a probability interpretation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[X]=\sum_\omega w_\omega X_\omega
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlExpectedLoss {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, w ω * X ω

end ActuarialValuation


