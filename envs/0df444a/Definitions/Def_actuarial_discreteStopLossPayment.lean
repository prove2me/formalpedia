-- Prove2me | Definitions.Def_actuarial_discreteStopLossPayment
-- name    : actuarial_discreteStopLossPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:25:00.822864+00:00
-- url     : https://prove2.me/theorems/622e55e1-ed93-4dc8-aa54-f4289102300c
-- title:
--   Payment by the reinsurer above an integer retention
-- statement:
--   A reinsurer pays the excess of realised aggregate claim above the contractual integer attachment point. Natural-number subtraction saturates at zero, so a loss below the deductible correctly produces no reinsurance payment.
--
--   **Mathematical statement**
--
--   $$
--   (s-d)_+=\max(s-d,0)
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def discreteStopLossPayment (claim deductible : ℕ) : ℕ :=
  claim - deductible

end ActuarialValuation


