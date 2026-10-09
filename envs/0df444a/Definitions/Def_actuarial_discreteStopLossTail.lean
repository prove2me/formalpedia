-- Prove2me | Definitions.Def_actuarial_discreteStopLossTail
-- name    : actuarial_discreteStopLossTail
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:55.617519+00:00
-- url     : https://prove2.me/theorems/88e2d27e-6d65-452d-8838-eab161ed6b98
-- title:
--   Probability of exceeding an integer stop-loss retention
-- statement:
--   The tail value is the finite sum of probability masses at aggregate losses strictly greater than the selected deductible. The inequality is strict: a claim exactly equal to attachment produces no stop-loss payment and does not enter this tail.
--
--   **Mathematical statement**
--
--   $$
--   T_B(d)=\sum_{s=d+1}^{B}w_s
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def discreteStopLossTail
  (w : ℕ → ℝ) (bound deductible : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1),
    if deductible < s then w s else 0

end ActuarialValuation


