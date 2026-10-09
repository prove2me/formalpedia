-- Prove2me | Definitions.Def_actuarial_deathYearEvent
-- name    : actuarial_deathYearEvent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T17:39:02.536976+00:00
-- url     : https://prove2.me/theorems/abae13df-0d19-47e9-bd48-83b5b98d1ea0
-- title:
--   Death during a specified curtate lifetime year
-- statement:
--   For policy year k+1, the death-year event consists of outcomes where curtate future lifetime K equals k.
--
--   $$
--   D_k=\{\omega:K(\omega)=k\}
--   $$
-- source:
--   *Life Contingencies*, Chapter 2 §2.4.3 (curtate lifetime), https://openacttextdev.github.io/LifeCon/C-ModelingLifeTimes.html

import Mathlib

namespace ActuarialValuation

def deathYearEvent {Ω : Type*} (K : Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | K ω = k}

end ActuarialValuation


