-- Prove2me | Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
-- name    : actuarial_wholeLifeAnnuityImmediatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:34:03.637227+00:00
-- url     : https://prove2.me/theorems/f6c00ffc-a82b-4994-8df7-cd65d7f66ce6
-- title:
--   Whole-life annuity payable in arrears
-- statement:
--   For each realised curtate lifetime K, this is the present value of unit payments at the end of policy years 1 through K, with no payment at time zero. This is the whole-life annuity in arrears described by textbook equations (3.11)–(3.12).
--
--   $$
--   Z_{\mathrm{WL,immediate}}(\omega)=\sum_{k=1}^{K(\omega)}v^k
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def wholeLifeAnnuityImmediatePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (K ω), v ^ (k + 1)

end ActuarialValuation


