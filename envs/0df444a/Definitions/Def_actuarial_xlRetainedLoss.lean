-- Prove2me | Definitions.Def_actuarial_xlRetainedLoss
-- name    : actuarial_xlRetainedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:35.644493+00:00
-- url     : https://prove2.me/theorems/d72662a2-e8d5-4faa-b16f-f001a414355d
-- title:
--   Excess-of-loss retained claim
-- statement:
--   The cedant retains the smaller of gross claim z and retention a, with nonnegative inputs required for insurance interpretation.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)=\min(z,a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlRetainedLoss (z a : ℝ) : ℝ := min z a

end ActuarialValuation


