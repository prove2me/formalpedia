-- Prove2me | Definitions.Def_actuarial_wholeLifeAnnuityDuePV
-- name    : actuarial_wholeLifeAnnuityDuePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T20:33:49.085322+00:00
-- url     : https://prove2.me/theorems/54833977-fc4f-4924-a5b2-479c8f63330d
-- title:
--   Whole-life annuity payable in advance
-- statement:
--   For each realised curtate lifetime K, this is the present value of unit payments at the start of policy years 0 through K, including the payment at time zero. This is the whole-life annuity in advance described by textbook equations (3.11)–(3.12).
--
--   $$
--   Z_{\mathrm{WL,due}}(\omega)=\sum_{k=0}^{K(\omega)}v^k
--   $$
-- source:
--   *Life Contingencies*, Chapter 3 §3.3.1 eqs (3.11)–(3.12), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def wholeLifeAnnuityDuePV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (K ω + 1), v ^ k

end ActuarialValuation


