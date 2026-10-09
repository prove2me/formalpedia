-- Prove2me | Definitions.Def_actuarial_discreteStopLossAggregateMean
-- name    : actuarial_discreteStopLossAggregateMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:26:32.110786+00:00
-- url     : https://prove2.me/theorems/940b5133-4408-445d-9164-21e420679c91
-- title:
--   Expected aggregate claim before reinsurance
-- statement:
--   The original insurer claim expectation is the sum of each bounded integer loss times its probability mass. This represents the gross portfolio claim expectation before allocation between a retained layer and stop-loss cover.
--
--   **Mathematical statement**
--
--   $$
--   \mu_B=\sum_{s=0}^{B}sw_s
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def discreteStopLossAggregateMean (w : ℕ → ℝ)
  (bound : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1), (s : ℝ) * w s

end ActuarialValuation


