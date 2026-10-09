-- Prove2me | Definitions.Def_actuarial_discreteStopLossPremium
-- name    : actuarial_discreteStopLossPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:40.006425+00:00
-- url     : https://prove2.me/theorems/02aeade8-6a48-424e-a306-ba2130a2d7e3
-- title:
--   Pure stop-loss premium over a bounded integer aggregate distribution
-- statement:
--   The expected payment for a bounded aggregate-claim model is the finite probability-weighted sum of all excess amounts above retention d. The loss grid runs exactly from zero through bound, and the formula has no variance loading or expense margin.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_B(d)=\sum_{s=0}^{B}(s-d)_+w_s
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

namespace ActuarialValuation

noncomputable def discreteStopLossPremium
  (w : ℕ → ℝ) (bound deductible : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (bound + 1),
    (discreteStopLossPayment s deductible : ℝ) * w s

end ActuarialValuation


