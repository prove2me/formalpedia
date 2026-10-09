-- Prove2me | Definitions.Def_actuarial_curtateSurvivalEvent
-- name    : actuarial_curtateSurvivalEvent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T19:11:12.260667+00:00
-- url     : https://prove2.me/theorems/47ab231d-ea1e-4ab4-a80f-269e8a7d68ca
-- title:
--   Curtate survival to maturity
-- statement:
--   This is the event that the life completes at least n years. It includes a life whose exact death time is maturity, because K counts completed years.
--
--   $$
--   E_n^{\ge}=\{\omega:K(\omega)\ge n\}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

def curtateSurvivalEvent {Ω : Type*} (K : Ω → ℕ) (n : ℕ) : Set Ω :=
  {ω | n ≤ K ω}

end ActuarialValuation


