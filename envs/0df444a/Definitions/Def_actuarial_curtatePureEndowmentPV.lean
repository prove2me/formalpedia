-- Prove2me | Definitions.Def_actuarial_curtatePureEndowmentPV
-- name    : actuarial_curtatePureEndowmentPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T19:13:10.223571+00:00
-- url     : https://prove2.me/theorems/f264f2d1-760f-42de-adc7-30c4927df2f6
-- title:
--   Curtate maturity payment for endowment assurance
-- statement:
--   This maturity payment is a unit benefit when the curtate lifetime is at least the term, discounted to maturity. It includes death exactly at maturity.
--
--   $$
--   Z_{\mathrm{maturity}}=v^n\mathbf1_{\{K\ge n\}}
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.2.4, equation (3.10), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent

namespace ActuarialValuation

noncomputable def curtatePureEndowmentPV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  v ^ n * (curtateSurvivalEvent K n).indicator (fun _ : Ω => (1 : ℝ)) ω

end ActuarialValuation


