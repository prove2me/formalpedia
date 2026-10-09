-- Prove2me | Definitions.Def_actuarial_endowmentAssurancePV
-- name    : actuarial_endowmentAssurancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T19:13:41.81164+00:00
-- url     : https://prove2.me/theorems/40043ca1-664d-4682-a2a3-75c69cbd0597
-- title:
--   Endowment assurance present value
-- statement:
--   This present value represents a unit benefit paid at the end of the year of death if death occurs within the term, or at maturity if the curtate lifetime is at least the term. These payment cases are exclusive.
--
--   $$
--   Z_{\mathrm{endow}}(\omega)=v^{\min(K(\omega)+1,n)}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

def endowmentAssurancePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  v ^ (min (K ω + 1) n)

end ActuarialValuation


