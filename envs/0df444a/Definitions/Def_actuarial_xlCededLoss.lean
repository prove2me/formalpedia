-- Prove2me | Definitions.Def_actuarial_xlCededLoss
-- name    : actuarial_xlCededLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:48.187981+00:00
-- url     : https://prove2.me/theorems/a55d1896-27dc-4c70-96ce-da4a75506dd4
-- title:
--   Excess-of-loss ceded claim
-- statement:
--   The reinsurer receives the excess of gross claim above the amount retained by the insurer.
--
--   **Mathematical statement**
--
--   $$
--   c(z,a)=z-\min(z,a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlCededLoss (z a : ℝ) : ℝ := z - min z a

end ActuarialValuation


