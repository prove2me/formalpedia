-- Prove2me | Definitions.Def_actuarial_discreteStopLossLimitedMean
-- name    : actuarial_discreteStopLossLimitedMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:26:18.199592+00:00
-- url     : https://prove2.me/theorems/d419c608-ffd8-48e9-979f-5b8359442c62
-- title:
--   Expected claim capped at the insurer's retention
-- statement:
--   The direct insurer retains the minimum of realised loss s and deductible d. This definition takes the weighted mean of those retained amounts on the finite aggregate grid, complementing the excess payment made by the stop-loss reinsurer.
--
--   **Mathematical statement**
--
--   $$
--   L_B(d)=\sum_{s=0}^{B}\min(s,d)w_s
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def discreteStopLossLimitedMean
  (w : ℕ → ℝ) (bound deductible : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1),
    (min s deductible : ℝ) * w s

end ActuarialValuation


