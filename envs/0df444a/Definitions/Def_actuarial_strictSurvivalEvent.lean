-- Prove2me | Definitions.Def_actuarial_strictSurvivalEvent
-- name    : actuarial_strictSurvivalEvent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T19:10:09.503842+00:00
-- url     : https://prove2.me/theorems/13f68d22-4373-4c34-8a13-64bc07addf4a
-- title:
--   Survival strictly beyond term n
-- statement:
--   This is the event that the exact lifetime extends strictly beyond the term. A life ending exactly at maturity is excluded.
--
--   $$
--   E_n^{>}=\{\omega:T(\omega)>n\}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.3, equation (3.9), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

def strictSurvivalEvent {Ω : Type*} (T : Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | (n : ℝ) < T ω}

end ActuarialValuation


