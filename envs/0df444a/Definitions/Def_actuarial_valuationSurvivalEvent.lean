-- Prove2me | Definitions.Def_actuarial_valuationSurvivalEvent
-- name    : actuarial_valuationSurvivalEvent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:15:58.669128+00:00
-- url     : https://prove2.me/theorems/8285c539-3ffd-4f89-afc9-bbb82d86bcbd
-- title:
--   In-force survival event
-- statement:
--   Defines the event that a policy remains in force at integer duration t.
--
--   **Mathematical statement**
--
--   $$
--   S_t=\{\omega:K(\omega)\ge t\}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
open MeasureTheory


namespace ActuarialValuation

def valuationSurvivalEvent {Ω : Type*} (K : Ω → ℕ) (t : ℕ) : Set Ω :=
  {ω | t ≤ K ω}

end ActuarialValuation


