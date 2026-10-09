-- Prove2me | Definitions.Def_actuarial_xlFiniteOptimalRetentionCost
-- name    : actuarial_xlFiniteOptimalRetentionCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:59:10.583706+00:00
-- url     : https://prove2.me/theorems/12db98cf-dffa-4adb-9b9e-b42a0ddf76e3
-- title:
--   Optimal cost among a finite nonempty retention menu
-- statement:
--   Minimum risk-adjusted cost over a finite nonempty menu of admissible retention amounts; separate nonnegativity conditions give insurance meaning.
--
--   **Mathematical statement**
--
--   $$
--   J^\star=\min_{a\in A}J_{\theta,\lambda}(\alpha_a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlRiskAdjustedRetentionCost
open MeasureTheory

namespace ActuarialValuation

noncomputable def xlFiniteOptimalRetentionCost {Ω A : Type*}
  [Fintype Ω] [Fintype A] [Nonempty A]
  (w z : Ω → ℝ) (retention : A → ℝ) (θ kap : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : A => xlRiskAdjustedRetentionCost w z θ kap (retention a))

end ActuarialValuation


